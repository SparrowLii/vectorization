# Auto Vectorization in Rust

## 1. Background

**SIMD**(Single Instruction Multiple Data) is a commonly used acceleration technology in computing scenarios. This technique improves program performance by replacing general assembly instructions with SIMD instructions provided by the CPU. These SIMD instructions use some special registers, which can put multiple general integer or floating point values at a time, just like a vector, so as to achieve the effect of performing multiple operations in one instruction cycle. So this technique is also called vectorization. 

LLVM provides some automatic vectorization optimization mechanisms, which can automatically perform SIMD optimization work in some scenarios. But in many other scenarios, we still need to manually use SIMD instructions to rewrite the program to get the SIMD acceleration effect.

The Rust compiler does a good job of generating proper LLVM IR to get SIMD instruction acceleration. And Rust developers currently have multiple ways to use these SIMD instructions:
· stdarch
· protable-SIMD
· use 'extern “platform-intrinsics” ' Abi directly

(I also made some contributions in stdarch last year)

But these ways require developers to rewrite their original code. This has several distinct drawbacks:

(1) Makes the code **complex and hard to read**, multiplying the size of the code

Here is an example that use `platform-intrinsic` to optimize the function which calculates the variance of an array:

origin code:

```rust
fn var(arr: &[f32]) -> f32 {
    let mut sq_sum = 0.;
    let mut sum = 0.;
    let len = arr.len() as f32;
    for i in arr {
        sum += i;
        sq_sum += i * i;
    }
    let ave = sum / len;
    sq_sum /  len - ave * ave
}
```

optimized code:

```rust
#![feature(platform_intrinsics, repr_simd)]

extern "platform-intrinsic" {
    pub fn simd_mul<T>(x: T, y: T) -> T;
    pub fn simd_add<T>(x: T, y: T) -> T;
    pub fn simd_reduce_add_unordered<T, U>(x: T) -> U;
}

const SIMD_LEN: usize = 64;
#[repr(simd)]
#[derive(Copy, Clone)]
pub struct SIMD([f32; SIMD_LEN]);

fn var(arr: &[f32]) -> f32 {
    let mut sq_sum = SIMD([0.; SIMD_LEN]);
    let mut sum = SIMD([0.; SIMD_LEN]);
    let len = arr.len() as f32;
    for i in 0..arr.len() / SIMD_LEN {
        let offset = i * SIMD_LEN;
        unsafe {
            let temp: SIMD = std::ptr::read_unaligned(&arr[offset] as *const f32 as *const SIMD);
            sum = simd_add(sum, temp);
            sq_sum = simd_add(sq_sum, simd_mul(temp, temp));
        }
    }
    let sq_sum: f32 = unsafe{
        simd_reduce_add_unordered(sq_sum)
    };
    let sum: f32 = unsafe{
        simd_reduce_add_unordered(sum)
    };
    let ave = sum / len;
    sq_sum /  len - ave * ave
}
```

(Additionally, because of the strict requirements on parameters of SIMD instructions, developers must additionally create a data structure with the #[repr(SIMD)] attribute, or use the `transmute` instruction to force the conversion.)

Or we can look at this example given in stdarch's [document](https://doc.rust-lang.org/stable/core/arch/):

```rust
// origin function
fn hex_encode_fallback(src: &[u8], dst: &mut [u8]) {
    fn hex(byte: u8) -> u8 {
        static TABLE: &[u8] = b"0123456789abcdef";
        TABLE[byte as usize]
    }

    for (byte, slots) in src.iter().zip(dst.chunks_mut(2)) {
        slots[0] = hex((*byte >> 4) & 0xf);
        slots[1] = hex(*byte & 0xf);
    }
}

// optimized function
#[target_feature(enable = "sse4.1")]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
unsafe fn hex_encode_sse41(mut src: &[u8], dst: &mut [u8]) {
    #[cfg(target_arch = "x86")]
    use std::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    use std::arch::x86_64::*;

    let ascii_zero = _mm_set1_epi8(b'0' as i8);
    let nines = _mm_set1_epi8(9);
    let ascii_a = _mm_set1_epi8((b'a' - 9 - 1) as i8);
    let and4bits = _mm_set1_epi8(0xf);

    let mut i = 0_isize;
    while src.len() >= 16 {
        let invec = _mm_loadu_si128(src.as_ptr() as *const _);

        let masked1 = _mm_and_si128(invec, and4bits);
        let masked2 = _mm_and_si128(_mm_srli_epi64(invec, 4), and4bits);

        // return 0xff corresponding to the elements > 9, or 0x00 otherwise
        let cmpmask1 = _mm_cmpgt_epi8(masked1, nines);
        let cmpmask2 = _mm_cmpgt_epi8(masked2, nines);

        // add '0' or the offset depending on the masks
        let masked1 = _mm_add_epi8(
            masked1,
            _mm_blendv_epi8(ascii_zero, ascii_a, cmpmask1),
        );
        let masked2 = _mm_add_epi8(
            masked2,
            _mm_blendv_epi8(ascii_zero, ascii_a, cmpmask2),
        );

        // interleave masked1 and masked2 bytes
        let res1 = _mm_unpacklo_epi8(masked2, masked1);
        let res2 = _mm_unpackhi_epi8(masked2, masked1);

        _mm_storeu_si128(dst.as_mut_ptr().offset(i * 2) as *mut _, res1);
        _mm_storeu_si128(
            dst.as_mut_ptr().offset(i * 2 + 16) as *mut _,
            res2,
        );
        src = &src[16..];
        i += 16;
    }

    let i = i as usize;
    hex_encode_fallback(src, &mut dst[i * 2..]);
}
```

(2) For those unfamiliar with SIMD, getting these speedups is **very difficult**. Although interested people can learn them from the document and open source code in our community, for companies that want to use this technology to optimize their code, this will increase a lot of time and labor costs.

To solve these problems, we can implement the auto-vectorization feature in the rust compiler.

## 2. Auto-Vectorization in Rust

I have initially implemented automatic vectorization based on rust1.60.0. All code changes including tests can be viewed in [this PR](https://github.com/SparrowLii/vectorization/pull/1) submitted in my personal repository. Below I will introduce the use of this feature through a few examples, and then briefly introduce the implementation of this feature.

Auto-vectorization is a feature based on **Rust mir**, since mir can clearly express the structure of a function.

It behaves like a normal **mir optimization pass**. But in order to make it usable, mir and some codegen functions need to be modified at a few points.

It automatically analyze and re-factor the **loop part** in mir, and to obtain SIMD acceleration in as many scenarios as possible while ensuring safety and program functionality.

### 2.1.1 Example: Sum of floating point numbers

 Test code is [here](https://github.com/SparrowLii/vectorization/blob/vectorization/mir-opt/vectorization/sum.rs)

We can see the following two functions:

```rust
#[vectorization]
fn func1(arr: &[f32]) -> f32 {
    let mut sum = 0.;
    for i in arr {
        sum += *i;
    }
    sum
}

fn func2(arr: &[f32]) -> f32 {
    let mut sum = 0.;
    for i in arr {
        sum += *i;
    }
    sum
}
```

For users, the only difference is that the #[vectorization] attribute is added above func1, indicating that automatic vectorization is enabled on this function. We call two functions separately in the `main` function and count the time they spend. After compiled and run with the `rustc -Copt-level=3 -Zmir-opt-level=4` command in the local `x86_64` environment, the results are as follows:

```
t1: 327
t2: 6519
ans1: 2201600
ans2: 2201600
```

We can see that the first function is almost 20 times faster than the second function.

### 2.1.2 More practical example: calculating the variance of an array

Calculating variance is a very commonly used function in the field of statistics. The test code is [here](https://github.com/SparrowLii/vectorization/blob/vectorization/mir-opt/vectorization/var.rs).

We can see the following two functions:

```rust
#[vectorization]
fn var1(arr: &[f32]) -> f32 {
    let mut sq_sum = 0.;
    let mut sum = 0.;
    let len = arr.len() as f32;
    for i in arr {
        sum += i;
        sq_sum += i * i;
    }
    let ave = sum / len;
    (sq_sum /  len - ave * ave).sqrt()
}

fn var2(arr: &[f32]) -> f32 {
    let mut sq_sum = 0.;
    let mut sum = 0.;
    let len = arr.len() as f32;
    for i in arr {
        sum += i;
        sq_sum += i * i;
    }
    let ave = sum / len;
    (sq_sum /  len - ave * ave).sqrt()
}
```

The difference between the two functions is still only whether to add the #[vectorization] attribute. After using the same compilation command and environment as before, the effect of running is as follows:

```
t1: 7
t2: 67
ans1: 28.667055
ans2: 28.649292
```

We can see that the first function is about 10 times faster than the second one. The result of the calculation is somewhat different, because the calling SIMD instruction results in a different order of floating-point operations, resulting in different rounding errors. There is currently no good solution to this problem. 

### 2.1.3 More complex example

We can look at this more complex example below. The test code is [here](https://github.com/SparrowLii/vectorization/blob/vectorization/mir-opt/vectorization/iter_simd.rs).

```rust
#[vectorization]
fn func1(src: &[f32], src2: &[f32], val: &mut [f32]) {
    let mut sum = 0.;
    for x in 0..src.len() {
        let v = src[x];
        sum += v * v;
        val[x] = src2[x] + sum;
    }
}
```

In this example, the value of the variable sum will be changed in each thorn loop based on the value in the previous loop, which can have a significant impact on the effect of auto-vectorization. We can check the result of running:

```
t1: 6984
t2: 7952
```

The optimization effect is not very significant, but there is still more than 13% efficiency improvement.

### 2.2 Implementation of Auto-vectorization

About 90% of the code changes are in the addition of a MIR optimization pass called `Vectorize`. It automatically analyze and re-factor the loop part in mir, and to obtain SIMD acceleration in as many scenarios as possible while ensuring safety and program functionality.

The remaining about 10% of the code are necessary changes to other parts of rustc. For example, add `VectorFunc` to the Terminator enumeration type of mir. This part of the code can be a temporary solution, or there may be a better implementation.

### 2.2.1 The main process of mir optimization pass

`Vectorize`pass will parse the loop structure in mir blocks, divide it into three parts `before loop`loop part`after loop`, re-factor the `loop part`. The three parts are then rejoined into the final mir.

<img src="img\1.PNG" style="zoom:80%;" />

There are three key steps in the refactoring process. They generate `Vec<OriginStmt>`,`Vec<VectStmt>` and the final mir respectively. `OriginStmt` and `VectStmt` are both intermediate representation `Enum` in the refactoring process.

<img src="img\2.PNG" style="zoom:80%;" />

step 1. Translate the original mir statements and terminators into the intermediate presentation layer `Vec<OriginStmt>` through the `resolve_stmt() `method, Then divide it into condition part and loop body part:

<img src="img\step1.PNG" style="zoom:80%;" />

The semantics represented by each type in `OriginStmt` are as follows:

| **OriginStmt Type**                     | **original mir semantics**                                   |
| --------------------------------------- | ------------------------------------------------------------ |
| CondiStorage                            | StorageLive/StorageDead statement for a loop condition variable |
| CondiSet / CondiGet                     | Set / Read the value of a loop condition variable            |
| AfterSet / AfterGet                     | Set / Read the value of a variable outside the loop body     |
| TempStorage                             | StorageLive/StorageDead statement for a temporary variables in the loop body |
| TempAssign                              | Set the value of a temporary variable using other temporary variables |
| BreakTerminator                         | The Terminator that jumps out of the loop, usually of type `SwitchInt` |
| SetCondiTerminator / GetCondiTerminator | Set / Read the value of a loop condition variable from a terminator, usually of type `Call` |
| TempFuncTerminator                      | Set / Read the value of a temporary variable from a terminator, usually of type `Call` |
| GotoTerminator / EndLoopTerminator      | `Goto` statements                                            |
| OtherTerminator                         | Special terminators, such as array bounds check assertions   |
| StoreAfter                              | Write the values from a vector to a variable (usually an array) outside the loop, only as a complement to some vectorized statements |

The key points in step1:
According to the scope of the variable, it is divided into three types: 
(1) loop condition variables
(2) variables outside the loop
(3) temporary variables within the loop

<img src="img\step1-1.PNG" style="zoom:67%;" />

The mapping of the original mir statement to the `OriginStmt` enumeration type is defined by the variable types involved in the statement, which in turn determines whether vectorization can be performed.

step 2. By parsing the OriginStmt array, translate the statements that can be vectorized into the corresponding VectStmt enumeration type; otherwise, keep it unchanged and use the InnerLoopStmt enum type to contain it:

<img src="img\step2.PNG" style="zoom:80%;" />

The semantics represented by each type in `VectStmt` are as follows:

| **VectStmt Type**           | **expressed semantics**                                      |
| --------------------------- | ------------------------------------------------------------ |
| StraightStmt / StraightTerm | Can be added directly to the final mir(like StorageLive / StorageDead / Goto) |
| BinOpAfterSet               | Set a value of a variable outside a loop using binary operators |
| BinOpAssign                 | Set a value of a temporary variable using binary operators   |
| ReadVector                  | Read a sequence of element values from an array              |
| VectorTerm                  | Call certain intrinsics that can be vectorized, such as `sqrtf32` |
| UseAssign                   | Use the Rvalue::Use statement to read a vector               |
| InnerLoopStmt               | Cannot be vectorized, use an inner loop to keep the original function unchanged |

What does `InnerLoopStmt` mean:
Assuming that the element length of the SIMD function is vector_len, the process of vectorization can be regarded as the process of loop unrolling and combining and executing some statements. Therefore, for the part that cannot be vectorized, a new loop needs to be created to execute it vector_len times to keep the program function unchanged.

step 3. Finally use generate_vector_section() method to generate mir statement from VectStmt array:

<img src="img\step3.PNG" style="zoom:80%;" />

### 2.2.2 other compiler changes

(1) Add a feature flag and attribute `vectorization`. We need a switch, like `#[inline]`, to decide whether to use auto-vectorization on a function. I think adding a `feature flag` is the best solution.

(2) Add a boolean type field `vector` to mir's `LocalDecl`. Because currently in automatic vectorization, the `Array` type is used as the type of the vector. In order for the `codegen_mir()` function to generate the correct `Layout` for these vectors, `LocalDecl` needs to add a field to indicate whether the `Local` value's Layout needs special handling.

(3)  Add a new mir Terminator type `VectorFunc`. A Terminator of type `Call` requires that the called intrinsic must have a `DefId`, but in auto-vectorization, the called intrinsic does not have a specific `DefId`. To highlight the difference, the current practice is to add a separate `VectorFunc` to indicate calling SIMD intrinsics.

(4) functions `codegen_intrinsic_call` and `generic_simd_intrinsic` in rustc_codegen_llvm/src/intrinsic.rs need some modification. `VectorFunc` will call these two functions in the codegen section. But because the called intrinsics do not have a `DefId`, the `codegen_intrinsic_call` method needs to be modified. In addition, because the vector type is `Array` rather than `AdtDef`, the `generic_simd_intrinsic` method also needs to determine whether the call comes from auto-vectorization and make some modifications.

### 2.3 Current major flaws in auto-vectorization

(1) The current implementation (multiply and add) has little effect of acceleration on integer operations. The main reason is that LLVM's own auto-vectorization already does this well. Performing auto-vectorized mir optimizations in these scenarios may instead lead to inefficiencies.

(2) More complex looping structures (Judgment and nested loops) are not yet supported. At present, vectorize can only deal with the scene of a single loop structure, which will gradually evolve in the future. 