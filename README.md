# Formale Systeme in LEAN

This repo contains the approach of formalizing the undergraduate Lecture ["Formale Systeme"](https://github.com/knowsys/FormaleSysteme) using [LEAN4](https://github.com/leanprover/lean4).
The project started and still emerges mostly through student projects. You are welcome to participate, just contact us!

## Notes on Setup:

Using `elan` / `lake`:  
```
lake build
```
This will download mathlib4 and build the project. Currently it might still break, because
mathlib4 has no releases yet. (Todo: update this when mathlib4 has a release)