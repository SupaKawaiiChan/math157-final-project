import Mathlib

/- Our goal in this homework is to show a working code fragment of my project, which is
to prove that if there is a bijective ring homomorphism between two rings, then the rings are
isomorphic. The formal statement is given as, "Let R and S be rings,
and let f: R→S be a bijective ring homomorphism. Then R and S are ring isomorphic."
The following code will follow the steps given in my homework 8.
1. Use surjectivity to define an inverse function.
2. Prove that the inverse function is a right and left inverse of f.
3. Prove that the inverse function for addition, multiplication and the identity.
4. Use the above lemmas to show that the inverse function is a ring homomorphism.
-/

variable {R S : Type*} [Ring R] [Ring S]
variable (f : R →+* S)
variable (hf : Function.Bijective f)

/- This is the first step, where I will define the inverse function.-/
noncomputable def inverseFunction : S → R := by
  intro s
  exact (hf.right s).choose

/-This is the second step. These set of lemmas will prove
that the inverse function is a right and left inverse of f.-/
lemma right_inverse : ∀ s : S, f (inverseFunction f hf s) = s := by
  intro s
  rw [inverseFunction]
  exact (hf.right s).choose_spec

lemma left_inverse : ∀ r : R, inverseFunction f hf (f r) = r := by
  intro r
  apply hf.1
  exact right_inverse f hf (f r)

/- For the third step, the next lemmas will be used to prove that the inverse function preserves
the identity and thering operations, addition and multiplication.-/

lemma inverse_map_zero : inverseFunction f hf 0 = 0 := by
  apply hf.1
  rw [right_inverse f hf]
  rw [map_zero]

lemma inverse_map_one : inverseFunction f hf 1 = 1 := by
  apply hf.1
  rw [right_inverse f hf]
  rw [map_one]

lemma inverse_map_add : ∀ s t : S, inverseFunction f hf (s + t)
= inverseFunction f hf s + inverseFunction f hf t := by
  intro s t
  apply hf.1
  rw[right_inverse f hf]
  rw[map_add]
  rw[right_inverse f hf]
  rw[right_inverse f hf]

lemma inverse_map_mul : ∀ s t : S, inverseFunction f hf (s * t)
= inverseFunction f hf s * inverseFunction f hf t := by
  intro s t
  apply hf.1
  rw[right_inverse f hf]
  rw[map_mul]
  rw[right_inverse f hf]
  rw[right_inverse f hf]

/-Finally, I used the previous lemmas to define the inverse function as a ring homomorphism.
Showing that the inverse preserves the ring operations, allowed me to define inverseRingHom,
which treats the inverse function as a ring homomorphism from S to R.
-/
noncomputable def inverseRingHom : S →+* R :=
    { toFun := inverseFunction f hf
      map_zero' := inverse_map_zero f hf
      map_one' := inverse_map_one f hf
      map_add' := inverse_map_add f hf
      map_mul' := inverse_map_mul f hf }

/-inally, I defined ringIsomorphism by combining the original function f with the inverse
function that I had constructed earlier. Using the left_inverse and right_inverse lemmas,
I showed that the two functions are inverses of each other. This completed the formalization
and proved that a bijective ring homomorphism induces a ring isomorphism.
-/
noncomputable def ringIsomorphism : R ≃+* S :=
    { toFun := f
      invFun := inverseFunction f hf
      left_inv := left_inverse f hf
      right_inv := right_inverse f hf
      map_add' := map_add f
      map_mul' := map_mul f }
