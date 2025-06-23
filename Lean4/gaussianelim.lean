/-
Copyright (c) 2025 Maria Joseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maria Joseph, Divakaran D
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.PEquiv
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Gaussian Elimination

In this file we define row exchange matrices as matrices obtained by swapping the ith and jth column of the identity matrix.  We show that multiplying a matrix M on the left by a row exchange matrix leads to swapping the ith and jth rows of M.  Building on Mathlib.LinearAlgebra.Matrix.Transvection we obtain a proof of the Gaussian elimination.  More precisely, we show that:

Given any matrix `M`, we can find a product of transvections and row exchange matrices `L` such `L * M` is an lower triangular matrix.

## Main definitions and results

* `rowEx (i j : n)` the matrix obtained by swapping the ith and jth row of an nxn identity matrix

* `EliminationStr` a structure that contains all the information to construct an elimination matrix

* `mul_rowEx_eq_swap` states that multiplying with a matrix M with rowEx i j on the left exchanges
  the ith row and the jth row of M with each other

* `rowEx_respects_inclusion` states that if `M` is the matrix obtained by exchanging the ith and jth rows
 of the `rxr` identity matrix, then the matrix obtained by exchanging the ith and jth rows of an
 `(r+1)x(r+1)` identity matrix is the block matrix whose blocks are `M`, `0`, `0`, `1`.

* `transvec_mul_rowEx_mul_lastcol` states that for every (r+1)x(r+1) matrix M ,there is a list of
  transvections and a row exchange matrix such that multiplying on the left with the rowEx and then
  the list of transvections will make M₍ᵢ,ᵣ₊₁₎ = 0 for every 1 ≤ i < r+1

* `exists_Listelimmatrix_eq_lowertriangular` states that given any matrix `M`, we can find a
  product of transvections and row exchange matrices `L` such that `L * M` is an lower triangular
  matrix.

## Tags

linear algerba, matrix, matrices, linear equations, Gaussian Elimination

-/

open Matrix BigOperators
open Equiv Equiv.Perm Finset Function

namespace matrix
open matrix
variable {m n k : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type*} [CommRing R]

variable {𝕜 : Type*} [Field 𝕜]

/-- `rowEx i j` is the matrix obtained by swapping the ith and jth row of an nxn identity matrix. -/
def rowEx (i j : n) : Matrix n n R :=
(Equiv.swap i j).toPEquiv.toMatrix

/-- `rowEx i i` is the identity matrix -/
theorem rowEx_i_i_eq_id (i : n) : rowEx i i = (1 : Matrix n n R) := by simp[rowEx]

/-- `rowEx i j` is precisely swapping the ith row of the identity matrix with the jth one and
swapping the jth row of the identity row with the ith one -/
theorem updateRow_eq_swap (i j : n)[Finite n] :
    updateRow (updateRow (1 : Matrix n n R) i ((1 :Matrix n n R) j)) j ((1 : Matrix n n R) i) =
    rowEx i j := by
  ext a b
  by_cases ha : i = a
  by_cases hb : j = b
  · simp[ha,hb]
    rw[rowEx,PEquiv.toMatrix_toPEquiv_eq]
    dsimp
    rw[Equiv.swap_apply_left,Matrix.updateRow_apply,Matrix.updateRow_self]
    by_cases hab : a = b
    rw[if_pos hab,ha,hab]
    rfl
    rw[if_neg hab,hb]
    rfl
  · rw [ha,rowEx]
    rw[PEquiv.toMatrix_toPEquiv_eq]
    dsimp
    rw[Equiv.swap_apply_left,Matrix.updateRow_apply,Matrix.updateRow_self]
    by_cases haj : a = j
    · rw[if_pos haj, haj]
      rfl
    · rw[if_neg haj]
      rfl
  · rw[rowEx]
    rw[PEquiv.toMatrix_toPEquiv_eq,Matrix.updateRow_apply,Matrix.updateRow_apply]
    dsimp
    rw[Equiv.swap_apply_def]
    by_cases haj : a = j
    · rw[if_pos haj,if_neg (ne_comm.mp ha),if_pos haj]
      rfl
    · rw[if_neg haj,if_neg (ne_comm.mp ha), if_neg haj, if_neg (ne_comm.mp ha)]
      rfl

/-Multiplying a matrix `M` on the left with `rowEx i j` exchanges the ith row and the jth row of `M`
 with each other -/
theorem rowEx_mul_eq_swap (i j : n)(M : Matrix n n R) : (rowEx i j : Matrix n n R) * M =
    updateRow (updateRow (M) i (M j)) j (M i) := by
  ext a b
  by_cases ha : i = a
  by_cases hb : j = b
  · simp[ha,hb]
    simp[Matrix.updateRow_apply]
    by_cases hab : a = b
    · simp[if_pos hab,rowEx,PEquiv.toMatrix_toPEquiv_mul,hab]
    · simp[if_neg hab,rowEx]
      rw[PEquiv.toMatrix_toPEquiv_mul]
      simp
  · simp[Matrix.updateRow_apply,ha]
    by_cases haj : a = j
    · rw[if_pos haj,rowEx,PEquiv.toMatrix_toPEquiv_mul]
      simp[haj]
    · rw[if_neg haj,rowEx,PEquiv.toMatrix_toPEquiv_mul]
      simp
  · simp[Matrix.updateRow_apply]
    by_cases haj : a = j
    · rw[if_pos haj,rowEx,PEquiv.toMatrix_toPEquiv_mul]
      simp[haj]
    · rw[if_neg haj,if_neg (ne_comm.mp ha),rowEx,PEquiv.toMatrix_toPEquiv_mul]
      simp[Equiv.swap_apply_def,if_neg (ne_comm.mp ha),if_neg haj]

/-- Multiplying a matrix `M` on the left by `rowEx i i` returns `M` -/
theorem mul_rowEx_i_i_eq (i :m) (M : Matrix m m R): (rowEx i i : Matrix m m R) * M = M := by
  simp[rowEx_mul_eq_swap]

namespace struct

open Sum Fin TransvectionStruct Pivot Matrix
variable (R n r)

/-- Let `A` be the block matrix with blocks `M`, `0`, `0`, `1` and `M'` be the matrix obtained by
exchanging the ith and jth row of `M`.  Then, the block matrix with blocks `M'`, `0`, `0`, `1` is
the equal to the matrix `A'` obtained by exchanging the ith and jth row of `A`  -/
theorem rowEx_respects_inclusion_1 (M: Matrix (Fin r) (Fin r) 𝕜) (i j : Fin r) :
    fromBlocks ((rowEx i j) * M) 0 0 (1: Matrix Unit Unit 𝕜) =
    (rowEx (inl i) (inl j)) * (fromBlocks M 0 0 (1 : Matrix Unit Unit 𝕜)) := by
  ext a b
  cases' a with a a <;> cases' b with b b
  any_goals {simp[rowEx_mul_eq_swap,Matrix.updateRow_apply]}

/-- Let `I'` be the matrix obtained by exchanging the ith and jth row of the rxr identity matrix.  Then, the block matrix formed by blocks `I'`, `0`, `0`, `1` is equal to the matrix obtained by exchaning the ith and jth row row of (r+1)x(r+1) identity matrix -/
theorem rowEx_respects_inclusion (i j : Fin r): fromBlocks (rowEx i j) 0 0 (1: Matrix Unit Unit 𝕜) =
    (rowEx (inl i) (inl j)) := by
  suffices fromBlocks ((rowEx i j) * (1 : Matrix (Fin r) (Fin r) 𝕜)) 0 0 (1: Matrix Unit Unit 𝕜) =
    (rowEx (inl i) (inl j)) * (1 : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) by
      simpa [Matrix.mul_one]
  rw[rowEx_respects_inclusion_1,Matrix.mul_one]
  simp

/- A structure that contains all the information to construct an elimination matrix-/
structure EliminationStr where
  /-- A list of transvection structures-/
  (L : List (TransvectionStruct n R))
  /-- and a single row exchange -/
  (i j: n)

namespace EliminationStr

variable {n R}

/-- Converts an elimination structure to the corresponding elimination matrix -/
def toElim (e : EliminationStr n R) : Matrix n n R :=
  List.prod (List.map toMatrix (e.L)) * (rowEx e.i e.j)

/-- Converts an elimination structure for nxn matrix to an elimination structure for (n+k)x(n+k)
matrix -/
def elimBlkIncl (e : EliminationStr n R ) : (EliminationStr (n ⊕ k) R ) where
  L := (List.map (sumInl k) (e.L))
  i := inl e.i
  j := inl e.j

/-- `toElim (elimBlkIncl e)` is the block matrix with blocks `toElim e`, `0`, `0`, `1` -/
theorem toElim_of_elimBlkIncl_eq_blkInc_of_toElim (e : EliminationStr (Fin r) 𝕜) :
    toElim (elimBlkIncl e) = fromBlocks (toElim e) 0 0 (1 : Matrix Unit Unit 𝕜) := by
  simp[toElim,elimBlkIncl,←rowEx_respects_inclusion ,sumInl_toMatrix_prod_mul]

/-- The natural inclusion of EliminationStr n to EliminationStr n+kLet `L` be a list of elimination structure for rxr matrices, `M` be an rxr matrix, `N` be a 1x1 matrix, and `O` be a 1xk matrix.  Let `M'` be the block matrix with blocks `M`, `0`, `O`, `N`. Let `A` be the matrix obtained by converting each element of `L` into a matrix and taking their product.  Let `A'` be the matrix obtained by    -/
theorem go (M : Matrix (Fin r) (Fin r) 𝕜) (L : List (EliminationStr (Fin r) 𝕜))
    (N : Matrix Unit Unit 𝕜) (O : Matrix Unit (Fin r) 𝕜) :
    List.prod (List.map (toElim ∘ elimBlkIncl) L) * fromBlocks M (0: Matrix (Fin r) Unit 𝕜) O N =
    fromBlocks (List.prod (List.map toElim L) * M) (0: Matrix (Fin r) Unit 𝕜) O N := by
  induction' L with t L IH
  · simp
  · simp[Matrix.mul_assoc, IH, toElim_of_elimBlkIncl_eq_blkInc_of_toElim, fromBlocks_multiply]

/-- List of k trivial (c is zero) transvections -/
def listId(k:ℕ) : List (Matrix (Sum (Fin k) Unit) (Sum (Fin k) Unit) 𝕜) :=
  List.ofFn fun i : Fin k ↦ transvection (inl i) (inr Unit.unit) (0:𝕜)

/--Product of listId is an identity matrix -/
theorem listId_prod_eq_id(r : ℕ) :
    List.prod (listId r) = (1 : (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) ) := by
  simp[listId]

/-- For every r+1 by r+1 matrix M ,there is a list of transvections and a rowEx matrix such that
 multiplying on the left with the rowEx and then the list of transvections will make
 M₍ᵢ,ᵣ₊₁₎ = 0 for every 1 ≤ i < r+1 -/
theorem transvec_mul_rowEx_mul_lastcol (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ i :Fin r ⊕ Unit, ∃ L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
    (∀ j : Fin r, (List.prod (List.map toMatrix L) * (((rowEx i (inr 1) :
    Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)) (inl j) (inr 1) = 0) := by
  by_cases hMne0: M (inr 1) (inr 1) ≠ 0
  --Case 1: Bottom-right entry is non-zero
  --Begin by creating the i and L that is required and inserting it in the goal
  · let a : Fin r ⊕ Unit := inr 1 -- a = r+1
    use a
    -- let N be the matrix obtained after exchanging the a-th row with the last row
    let N : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜 :=
      (((rowEx a (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)
    have hNM: N = M := by exact mul_rowEx_i_i_eq a M
    let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
      List.ofFn fun i : Fin r ↦
      ⟨inl i, inr 1, by simp, - N (inl i) (inr 1) / N (inr 1) (inr 1)⟩
    refine' ⟨L,_⟩
    intro j
    have hLN : List.map toMatrix L = listTransvecCol N := by
        simp [L,hNM,transvection,listTransvecCol]
        rfl
    have h1: rowEx a (inr 1) * M = N := by rfl
    rw[hLN,h1,listTransvecCol_mul_last_col]
    rw[hNM]
    exact hMne0
  --Case 2: Bottom-right entry is zero
  · push_neg at hMne0

  /-Within the Second Case considering two cases when atleast one entry in last column is non-zero
  and when all entries are zero-/

    by_cases hexistsNon0: (∃ i : Fin r, M (inl i) (inr 1) ≠ 0)
    --Case 2.1: atleast one entry in the last column is non-zero
    · rcases hexistsNon0 with ⟨i, hi⟩
      /-if there is atleast one non-zero element in last column, you can make the M₍ᵣ₊₁,ᵣ₊₁₎
       non-zero using rowEx -/
      · have hn : (((rowEx (inl i) (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)
          * M) (inr 1) (inr 1) ≠ 0) := by
         rw[rowEx_mul_eq_swap]
         rw[Matrix.updateRow_self]
         exact hi
         --Repeating a proof similar to Case 1 since M₍ᵣ₊₁,ᵣ₊₁₎ is non-zero
        let a : Fin r ⊕ Unit := inl i
        use a
        let N: Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜 := (((rowEx a (inr 1) :
          Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)
        have h1: rowEx a (inr 1) * M = N := by rfl
        let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
         List.ofFn fun i : Fin r ↦
           ⟨inl i, inr 1, by simp, - N (inl i) (inr 1) / N (inr 1) (inr 1)⟩
        refine' ⟨L,_⟩
        intro j
        have hLN : List.map toMatrix L = listTransvecCol N := by
          simp [L,N,h1,listTransvecCol,transvection]
          rfl
        rw[hLN]
        rw[listTransvecCol_mul_last_col]
        exact hn
    --Case 2.2:  all entries in the last column are zero
    · push_neg at hexistsNon0
      let a : Fin r ⊕ Unit := inr 1
      use a
      ---if all entries in the last column are zero L can be a list of identity matrices
      let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
       List.ofFn fun i : Fin r ↦
         ⟨inl i, inr 1, by simp, 0⟩
      use L
      intro j
      have hL : List.map toMatrix L = listId r := by
        refine List.map_eq_iff.mpr ?_
        intro i
        simp [listId,L,]
        exact List.getElem?_replicate
      rw[hL,listId_prod_eq_id,Matrix.one_mul,rowEx_i_i_eq_id,Matrix.one_mul]
      exact hexistsNon0 j

/-- Given a matrix `M`, there exists an elimination structure `N` such that when we multiply `M` on
the left with the corresponding elimination matrix (`toElim N`), the first r entries of the last
column of the resultant matrix are zero -/
theorem exists_elimmatrix_mul_lastcol (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃(N : EliminationStr (Fin r ⊕ Unit) 𝕜), (∀ j : Fin r , ((toElim N) * M) (inl j) (inr 1) = 0) := by
  · have TH : ∃ i :Fin r ⊕ Unit, ∃ L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
    (∀ j : Fin r,
    (List.prod (List.map toMatrix L) * (((rowEx i (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜))
    * M)) (inl j) (inr 1) = 0):= by
      exact transvec_mul_rowEx_mul_lastcol r M
    cases TH with
    |intro k TH =>
    cases TH with
    |intro L' TH =>
    simp[toElim]
    let N': EliminationStr (Fin r ⊕ Unit) 𝕜 :=
    ⟨L',k,(inr 1)⟩
    exists N'
    simp[N']
    suffices  ∀ (j : Fin r), (List.prod (List.map toMatrix L') * ((rowEx k (inr 1) :
      Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) * M)) (inl j) (inr 1) = 0 by
        simp[Matrix.mul_assoc]
        exact TH
    exact TH

end EliminationStr

open EliminationStr

/-- Given any matrix `M`, we can find a product of transvections and row exchange matrices `L` such
that `L * M` is an lower triangular matrix -/
theorem exists_list_elimmatrix_mul_eq_lowertriangular (IH : ∀ (M : Matrix (Fin r) (Fin r) 𝕜),
    ∃ (E : List (EliminationStr (Fin r) 𝕜)),
    (List.prod (List.map toElim E) * M).BlockTriangular OrderDual.toDual)
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃(E₁ : List (EliminationStr (Fin r ⊕ Unit) 𝕜)),
    (List.prod (List.map toElim E₁) * M).BlockTriangular OrderDual.toDual := by
  have HM : ∃ N : EliminationStr (Fin r ⊕ Unit) 𝕜, ∀ (j : Fin r),
    (toElim N * M) (inl j) (inr Unit.unit) = 0 := by
   exact exists_elimmatrix_mul_lastcol r M
  cases HM with
  |intro N HM =>
  let M' := N.toElim * M
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L, h₀⟩
  set Mₐ := toBlocks₂₁ M'
  set c := toBlocks₂₂ M'
  refine'⟨List.map (elimBlkIncl) L ++ [N],_⟩
  suffices (List.prod (List.map (toElim ∘ elimBlkIncl) L) * M').BlockTriangular OrderDual.toDual by
    simpa[Matrix.mul_assoc]
  have H : M' = fromBlocks (M'') 0 Mₐ c := by
    have X : toBlocks₁₂ (M') = 0 := by
      ext a b
      simp[toBlocks₁₂]
      exact HM a
    rw[←X]
    exact Eq.symm (fromBlocks_toBlocks M')
  rw[H,go]
  simpa[BlockTriangular]
