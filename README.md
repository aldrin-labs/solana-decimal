# Error

There are two kinds of errors supported by this crate. The default one is
[`anyhow::Error`](https://docs.rs/anyhow/latest/anyhow/). If you use this crate
on Solana, you can include the dependency with:

```
solana-decimal = { default-features = false, features = ["anchor"] }
```

# `u192`

For decimal representation we use `u192` type which consists of 3 `u64`
integers. That is, `u192` is an unsigned integer of 24 bytes. A unit
representing one is a [wad][wiki-significand] and its value is $`10^{18}`$.
Therefore, first eighteen decimal digits represent fraction.

What follows are some snippets which illustrate how to convert between types in
typescript.

```typescript
import { BN } from "@project-serum/anchor";

type U192 = [BN, BN, BN];
const ONE_WAD = new BN(10).pow(new BN(18));
```

```typescript
function numberToU192(n: number): U192 {
  if (n < 0) {
    throw new Error("u192 is unsigned, number cannot be less than zero");
  }

  const wad = n < 1 ? ONE_WAD.div(new BN(1 / n)) : ONE_WAD.mul(new BN(n));
  const bytes = wad.toArray("le", 3 * 8); // 3 * u64

  const nextU64 = () => new BN(bytes.splice(0, 8), "le");
  return [nextU64(), nextU64(), nextU64()];
}
```

```typescript
function u192ToBN(u192: U192 | BN[] | { u192: U192 | BN[] }): BN {
  // flatten the input
  u192 = Array.isArray(u192) ? u192 : u192.u192;

  if (u192.length !== 3) {
    throw new Error("u192 must have exactly 3 u64 BN");
  }

  const ordering = "le";
  return new BN(
    [
      ...u192[0].toArray(ordering, 8),
      ...u192[1].toArray(ordering, 8),
      ...u192[2].toArray(ordering, 8),
    ],
    ordering
  );
}
```

<!-- References -->

[wiki-significand]: https://en.wikipedia.org/wiki/Significand
