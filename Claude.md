The goal is to adjust the dimension from 4 space-time dimensions to 3. The original lean project's folder @OSforGFF is for space-time dimension 4.  We are working on @OSforGFFin3D, to make analogous work for space-time dimension 3.

See @docs/dimension_dependence.md for a description of @OSforGFF and what needs to be adjusted.

Do not change any files in @OSforGFF/ folder.

Most of our work will be in @OSforGFFin3D/ folder.

- First stage: introduce a function `besselKhalf := besselK (1/2)` at the beginning of @OSforGFFin3D/BesselFunction.lean, right after the definition of `besselK`.

- Second stage: Change @OSforGFFin3D/BesselFunction.lean generalizing `BesselK1` to `BesselK`.  `BesselK` is already defined in that file.  Keep that definition and adjust all of the Lean proofs in that file accordingly. 

- Third stage: In files, mentioned in @docs/dimension_dependence.md, where `BesselK1` is used, change it to `BesselKhalf` and adjust the proofs accordingly.

