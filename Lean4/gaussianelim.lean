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

In this file we define row exchange matrices as matrices obtained by swapping the ith and jth
column of the identity matrix.  We show that multiplying a matrix M on the left by a row exchange
matrix leads to swapping the ith and jth rows of M.  Building on Mathlib.LinearAlgebra.Matrix.
Transvection we obtain a proof of the Gaussian elimination.  More precisely, we show that:

Given any matrix `M`, we can find a product of transvections and row exchange matrices `L` such
that `L * M` is an lower triangular matrix.

## Main definitions and results

* `rowEx (i j : n)` the matrix obtained by swapping the ith and jth row of an nxn identity matrix

* `EliminationStr` a structure that contains all the information to construct an elimination matrix

* `mul_rowEx_eq_swap` states that multiplying with a matrix M with rowEx i j on the left exchanges
  the ith row and the jth row of M with each other

* `rowEx_respects_inclusion` states that if `M` is the matrix obtained by exchanging the ith and
jth rows of the `rxr` identity matrix, then the matrix obtained by exchanging the ith and jth rows
of an `(r+1)x(r+1)` identity matrix is the block matrix whose blocks are `M`, `0`, `0`, `1`.

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
variable {m n k : Type*} [DecidableEq n] [DecidableEq m] [Fintype m]

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
  . by_cases hb : j = b
    · simp[ha,hb]
      rw[rowEx,PEquiv.toMatrix_toPEquiv_eq]
      dsimp
      rw[Equiv.swap_apply_left,Matrix.updateRow_apply,Matrix.updateRow_self]
      by_cases hab : a = b
      . rw[if_pos hab,ha,hab]
        rfl
      . rw[if_neg hab,hb]
        rfl
    · rw [ha,rowEx,PEquiv.toMatrix_toPEquiv_eq]
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
theorem rowEx_mul_eq_swap (i j : n) (M : Matrix n n R) [Fintype n] :
    (rowEx i j : Matrix n n R) * M = updateRow (updateRow (M) i (M j)) j (M i) := by
  ext a b
  by_cases ha : i = a
  . by_cases hb : j = b
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
  cases' a with ha1 ha2
  . cases' b with hb1 hb2
    . simp[rowEx_mul_eq_swap,Matrix.updateRow_apply]
    . simp[rowEx_mul_eq_swap,Matrix.updateRow_apply]
  . cases' b with hb1 hb2
    . simp[rowEx_mul_eq_swap,Matrix.updateRow_apply]
    . simp[rowEx_mul_eq_swap,Matrix.updateRow_apply]


/-- Let `I'` be the matrix obtained by exchanging the ith and jth row of the rxr identity matrix.
Then, the block matrix formed by blocks `I'`, `0`, `0`, `1` is equal to the matrix obtained by
exchaning the ith and jth row row of (r+1)x(r+1) identity matrix -/
theorem rowEx_respects_inclusion (i j : Fin r):
    fromBlocks (rowEx i j) 0 0 (1: Matrix Unit Unit 𝕜) = (rowEx (inl i) (inl j)) := by
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
def toElim (e : EliminationStr n R) [Fintype n] : Matrix n n R :=
  List.prod (List.map toMatrix (e.L)) * (rowEx e.i e.j)

theorem Elim_mk [Fintype n] (i j : n) (L : List (TransvectionStruct n R)) :
    toElim ⟨L,i,j⟩ = List.prod (List.map toMatrix L) * (rowEx i j):=
  rfl


/-- Converts an elimination structure for nxn matrix to an elimination structure for (n+k)x(n+k)
matrix -/
def elimBlkIncl (e : EliminationStr n R ) : (EliminationStr (n ⊕ k) R ) where
  L := (List.map (sumInl k) (e.L))
  i := inl e.i
  j := inl e.j

/-- The natural inclusion of EliminationStr n to EliminationStr n+k. Let `L` be a list of elimination
structure for rxr matrices, `M` be an rxr matrix, `N` be a 1x1 matrix, and `O` be a 1xk matrix.
Let `M'` be the block matrix with blocks `M`, `0`, `O`, `N`. Let `A` be the matrix obtained by
converting each element of `L` into a matrix and taking their product.  Let `A'` be the matrix
obtained by    -/
theorem elimBlkIncl_toElim_prod_mul (M : Matrix (Fin r) (Fin r) 𝕜) (L : List (EliminationStr (Fin r) 𝕜))
    (N : Matrix Unit Unit 𝕜) (O : Matrix Unit (Fin r) 𝕜) :
    List.prod (List.map (toElim ∘ elimBlkIncl) L) * fromBlocks M (0: Matrix (Fin r) Unit 𝕜) O N =
    fromBlocks (List.prod (List.map toElim L) * M) (0: Matrix (Fin r) Unit 𝕜) O N := by
  induction' L with e L IH
  · simp
  · simp[Matrix.mul_assoc, IH, toElim,elimBlkIncl,←rowEx_respects_inclusion ,sumInl_toMatrix_prod_mul, fromBlocks_multiply]

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
    ∃ i : Fin r ⊕ Unit, ∃ L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜), ∀ j : Fin r,
    (List.prod (List.map toMatrix L) * (((rowEx i (inr 1) :
    Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)) (inl j) (inr 1) = 0 := by
  by_cases hMne0: M (inr 1) (inr 1) ≠ 0
  --Case 1: Bottom-right entry is non-zero
  --Begin by creating the i and L that is required and inserting it in the goal
  · use inr 1
    let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
      List.ofFn fun i : Fin r ↦
      ⟨inl i, inr 1, by simp, - M (inl i) (inr 1) / M (inr 1) (inr 1)⟩
    use L
    intro j
    have hLN : List.map toMatrix L = listTransvecCol M := by
        simp [L,transvection,listTransvecCol]
        rfl
    have ha: rowEx (inr 1) (inr 1) * M = M := by exact mul_rowEx_i_i_eq (inr 1) M
    rw[hLN,ha,listTransvecCol_mul_last_col]
    exact hMne0
  --Case 2: Bottom-right entry is zero
  · push_neg at hMne0
    by_cases hexistsNon0: (∃ i : Fin r, M (inl i) (inr 1) ≠ 0)
    --Case 2.1: atleast one entry in the last column is non-zero
    · cases' hexistsNon0 with i hi
      /-if there is atleast one non-zero element in last column, you can make the M₍ᵣ₊₁,ᵣ₊₁₎
       non-zero using rowEx -/
      · have hn : (((rowEx (inl i) (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)
          * M) (inr 1) (inr 1) ≠ 0) := by
         rw[rowEx_mul_eq_swap]
         rw[Matrix.updateRow_self]
         exact hi
         --Repeating a proof similar to Case 1 since M₍ᵣ₊₁,ᵣ₊₁₎ is non-zero
        use inl i
        let N: Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜 := (rowEx (inl i) (inr 1)) * M
        let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
         List.ofFn fun i : Fin r ↦
           ⟨inl i, inr 1, by simp, - N (inl i) (inr 1) / N (inr 1) (inr 1)⟩
        use L
        intro j
        have hLN : List.map toMatrix L = listTransvecCol N := by
          simp [L,N,listTransvecCol,transvection]
          rfl
        rw[hLN,listTransvecCol_mul_last_col]
        exact hn
    --Case 2.2:  all entries in the last column are zero
    · push_neg at hexistsNon0
      use inr 1
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
    ∃ N : EliminationStr (Fin r ⊕ Unit) 𝕜,
    ∀ j : Fin r, ((toElim N) * M) (inl j) (inr 1) = 0 := by
  rcases transvec_mul_rowEx_mul_lastcol r M with ⟨k, L', hLC⟩
  let N' : EliminationStr (Fin r ⊕ Unit) 𝕜 := ⟨L', k, inr 1⟩
  use N'
  simp [toElim, N', Matrix.mul_assoc]
  exact hLC


variable {p}

/--Reindexing-/
def elimStrReindex (e : n ≃ p) (e' : EliminationStr n 𝕜) : EliminationStr p 𝕜 where
  i := e e'.i
  j := e e'.j
  L := (List.map (TransvectionStruct.reindexEquiv e) (e'.L))

variable [Fintype n] [Fintype p] [DecidableEq p]

theorem toMatrix_elimStrReindex (e : n ≃ p) (E : EliminationStr n 𝕜) :
    toElim (E.elimStrReindex  e) = reindexAlgEquiv 𝕜 _ e (toElim E) := by
  rcases E with ⟨ L, i, j⟩
  simp only [toElim, elimStrReindex]
  have : (reindexAlgEquiv 𝕜 𝕜 e) ((List.map toMatrix L).prod * rowEx i j) =
  (reindexAlgEquiv 𝕜 𝕜 e) ((List.map toMatrix L).prod) * (reindexAlgEquiv 𝕜 𝕜 e) (rowEx i j) :=by
    simp [AlgEquiv.map_mul']
  rw[this]
  have h2: rowEx (e i) (e j) = (reindexAlgEquiv 𝕜 𝕜 e) (rowEx i j):= by
    rw[reindexAlgEquiv_apply]
    rw[reindex_apply]
    ext a b
    rw[submatrix_apply]
    simp[PEquiv.toMatrix_toPEquiv_eq, rowEx]
    split_ifs with h1 h2 h3
    any_goals rfl
    any_goals rw [Equiv.swap_apply_def] at h1
    any_goals rw [Equiv.swap_apply_def] at h2
    any_goals rw [Equiv.swap_apply_def] at h3
    any_goals simp
    any_goals split_ifs at h1 with h11 h12
    any_goals split_ifs at h2 with h21 h22
    any_goals split_ifs at h3 with h31 h32
    any_goals apply e.apply_eq_iff_eq_symm_apply.mp at h1
    any_goals apply e.symm_apply_eq.mpr at h11
    exact absurd h1 h2
    exact absurd h11 h21
    exact absurd h11 h21
    any_goals apply e.symm_apply_eq.mp at h21
    exact absurd h21 h11
    exact absurd h1 h2
    any_goals apply e.symm_apply_eq.mpr at h12
    exact absurd h12 h22
    exact absurd h21 h11
    any_goals apply e.symm_apply_eq.mp at h22
    exact absurd h22 h12
    rw [h1] at h2
    rw[←ne_eq] at h2
    exact h2 rfl
    any_goals apply e.apply_eq_iff_eq_symm_apply.mpr at h3
    exact absurd h3 h1
    exact absurd h11 h31
    any_goals apply e.symm_apply_eq.mp at h31
    exact absurd h11 h31
    exact absurd h31 h11
    exact absurd h3 h1
    any_goals apply e.symm_apply_eq.mp at h32
    exact absurd h12 h32
    exact absurd h31 h11
    exact absurd h32 h12
    apply e.eq_symm_apply.mpr at h3
    simp at h3
    exact absurd h3 h1
  rw[←h2]
  simp only [toElim, reindexAlgEquiv_apply, reindex_apply]
  simp [toMatrix_reindexEquiv_prod]


end EliminationStr

open EliminationStr

/-- Given any matrix `M`, we can find a product of transvections and row exchange matrices `L` such
that `L * M` is an lower triangular matrix -/
theorem exists_list_elimmatrix_mul_eq_lowertriangular
    (IH : ∀ (M : Matrix (Fin r) (Fin r) 𝕜),
      ∃ E : List (EliminationStr (Fin r) 𝕜),
      (List.prod (List.map toElim E) * M).BlockTriangular OrderDual.toDual)
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃(E₁ : List (EliminationStr (Fin r ⊕ Unit) 𝕜)),
      (List.prod (List.map toElim E₁) * M).BlockTriangular OrderDual.toDual := by
  have hNLC : ∃ N : EliminationStr (Fin r ⊕ Unit) 𝕜, ∀ (j : Fin r),
    (toElim N * M) (inl j) (inr Unit.unit) = 0 := by
   exact exists_elimmatrix_mul_lastcol r M
  cases hNLC with
  |intro N hLC =>
  let M' := N.toElim * M
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L, h₀⟩
  set Mₐ := toBlocks₂₁ M'
  set c := toBlocks₂₂ M'
  refine'⟨List.map (elimBlkIncl) L ++ [N],_⟩
  suffices (List.prod (List.map (toElim ∘ elimBlkIncl) L) * M').BlockTriangular OrderDual.toDual by
    simpa[Matrix.mul_assoc]
  have hM' : M' = fromBlocks (M'') 0 Mₐ c := by
    have X : toBlocks₁₂ (M') = 0 := by
      ext a b
      simp[toBlocks₁₂]
      exact hLC a
    rw[←X]
    exact Eq.symm (fromBlocks_toBlocks M')
  rw[hM']
  rw[elimBlkIncl_toElim_prod_mul]
  simpa[BlockTriangular]


/- Attempts at proving the more general result -/

variable {p} [Fintype p] [Fintype n] [DecidableEq n] [DecidableEq p]

theorem reindexing [LT nᵒᵈ] [LT pᵒᵈ] (M : Matrix p p 𝕜) (e : p ≃ n)
    (H :
      ∃ E : List (EliminationStr n 𝕜),
      (List.prod (List.map toElim E) * Matrix.reindexAlgEquiv 𝕜 _ e M).BlockTriangular OrderDual.toDual):
    ∃ E : List (EliminationStr p 𝕜),
      (List.prod (List.map toElim E) * M).BlockTriangular OrderDual.toDual := by
  rcases H with ⟨E, hE⟩
  let elimStrReindex : EliminationStr n 𝕜 → EliminationStr p 𝕜 :=
    fun es => {
      L := es.L.map (reindexEquiv e.symm)
      i := e.symm es.i
      j := e.symm es.j
    }
  refine ⟨E.map elimStrReindex, ?_⟩
  sorry


theorem final (n : Type) [Fintype n] [DecidableEq n] [LT nᵒᵈ]
    (M : Matrix n n 𝕜) : ∃ E₁ : List (EliminationStr n 𝕜),
      (List.prod (List.map toElim E₁) * M).BlockTriangular OrderDual.toDual := by
  suffices ∀ cn, Fintype.card n = cn →
    ∃ E₁ : List (EliminationStr n 𝕜),
      (List.prod (List.map toElim E₁) * M).BlockTriangular OrderDual.toDual
    by exact this (Fintype.card n) rfl
  intro cn hcn
  induction cn generalizing n M with
  | zero =>
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hcn
    use []
    simp [BlockTriangular]
  | succ r IH =>
    have e : n ≃ Fin r ⊕ Unit := by
      refine Fintype.equivOfCardEq ?_
      rw [hcn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    sorry
