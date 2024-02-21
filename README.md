# Formale Systeme in LEAN

This repo contains the approach of formalizing the undergraduate Lecture ["Formale Systeme"](https://github.com/knowsys/FormaleSysteme) using [LEAN4](https://github.com/leanprover/lean4).
The project started and still emerges mostly through student projects. You are welcome to participate, just contact us!

## Notes on Setup:

Using [`elan`](https://github.com/leanprover/elan) / `lake`:  
```
lake build
```
This will download mathlib4 and build the project.  
To prevent building mathlib yourself, you can run the following to fetch precompiled files.
```
lake exe cache get
```
