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

open Matrix BigOperators
open Equiv Equiv.Perm Finset Function

namespace matrix
open matrix
variable {m n p : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m][DecidableEq p]

variable {R : Type*} [CommRing R]

variable {𝕜 : Type*} [Field 𝕜]

/-nxn Identity matrices with the ith and jth row swapped is defined by RowEx i j. -/

def RowEx (i j : n): Matrix n n R :=
(Equiv.swap i j).toPEquiv.toMatrix



--RowEx i i is the identity matrix
theorem RowExii_eq_id (i : n): RowEx i i = (1 : Matrix n n R) := by simp[RowEx]

/-RowEx i j is precisely swapping the ith row of the identity matrix with the jth one and swapping
 the jth row of the identity row with the ith one -/

theorem updaterow_eq_swap (i j : n)[Finite n]:
updateRow (updateRow (1 : Matrix n n R) i ((1 :Matrix n n R) j)) j ((1 : Matrix n n R) i) =
RowEx i j := by
ext a b
by_cases ha : i = a; by_cases hb : j = b
· simp[ha,hb]
  rw[RowEx,PEquiv.toMatrix_toPEquiv_eq]
  dsimp
  rw[Equiv.swap_apply_left,Matrix.updateRow_apply,Matrix.updateRow_self]
  by_cases hab : a = b
  rw[if_pos hab,ha,hab]
  rfl
  rw[if_neg hab,hb]
  rfl
· rw [ha,RowEx]
  rw[PEquiv.toMatrix_toPEquiv_eq]
  dsimp
  rw[Equiv.swap_apply_left,Matrix.updateRow_apply,Matrix.updateRow_self]
  by_cases haj : a = j
  · rw[if_pos haj, haj]
    rfl
  · rw[if_neg haj]
    rfl
· rw[RowEx]
  rw[PEquiv.toMatrix_toPEquiv_eq,Matrix.updateRow_apply,Matrix.updateRow_apply]
  dsimp
  rw[Equiv.swap_apply_def]
  by_cases haj : a = j
  · rw[if_pos haj,if_neg (ne_comm.mp ha),if_pos haj]
    rfl
  · rw[if_neg haj,if_neg (ne_comm.mp ha), if_neg haj, if_neg (ne_comm.mp ha)]
    rfl

-- It is commutative
theorem RowEx_comm (i j : n) :
 RowEx i j = (RowEx j i : Matrix n n R)  := by
 simp[RowEx]
 rw[Equiv.swap_comm]


/-Multiplying with a matrix M with RowEx i j on the left exchanges the ith row and the jth row of M
 with each other -/

theorem RowExmul_eq_swap (i j: n)(M : Matrix n n R) : (RowEx i j : Matrix n n R) * M =
updateRow (updateRow (M) i (M j)) j (M i) := by
ext a b
by_cases ha : i = a; by_cases hb : j = b
· simp[ha,hb]
  simp[Matrix.updateRow_apply]
  by_cases hab : a = b;
  · simp[if_pos hab,RowEx,PEquiv.toMatrix_toPEquiv_mul,hab]
  · simp[if_neg hab,RowEx]
    rw[PEquiv.toMatrix_toPEquiv_mul]
    simp
· simp[Matrix.updateRow_apply,ha]
  by_cases haj : a = j;
  · rw[if_pos haj,RowEx,PEquiv.toMatrix_toPEquiv_mul]
    simp[haj]
  · rw[if_neg haj,RowEx,PEquiv.toMatrix_toPEquiv_mul]
    simp
· simp[Matrix.updateRow_apply]
  by_cases haj : a = j;
  · rw[if_pos haj,RowEx,PEquiv.toMatrix_toPEquiv_mul]
    simp[haj]
  · rw[if_neg haj,if_neg (ne_comm.mp ha),RowEx,PEquiv.toMatrix_toPEquiv_mul]
    simp[Equiv.swap_apply_def,if_neg (ne_comm.mp ha),if_neg haj]


theorem RowExid (i :m) (M : Matrix m m R):
(RowEx i i : Matrix m m R) * M = M := by
simp[RowExmul_eq_swap]


--RowEx i j and RowEx j i are inverses of each other
theorem RowExij_mul_Rowexji_eq_id [Finite n](i j : n): RowEx j i * RowEx i j = (1 : Matrix n n R) := by
rw[RowExmul_eq_swap,←updaterow_eq_swap,Matrix.updateRow_self]
ext a b
by_cases hai : i = a ; by_cases hbj : j = b
· rw[hai,hbj,Matrix.updateRow_apply,if_pos rfl]
· rw[hai,Matrix.updateRow_self]
· simp[Matrix.updateRow_apply,if_neg (ne_comm.mp hai)]
  by_cases haj : a = j;
  · rw[if_pos haj,if_neg, haj]
    exact Ne.trans_eq hai haj
  · rw[if_neg haj,if_neg haj]



--RowEx i j is the inverse of itself
theorem RowExii_mulself_id (i j : n) : RowEx i j * RowEx i j = (1 : Matrix n n R) := by
rw[RowExmul_eq_swap,←updaterow_eq_swap,Matrix.updateRow_self]
ext a b
by_cases hai : i = a ; by_cases hbj : j = b
· simp[hai,hbj,Matrix.updateRow_apply]
  by_cases hab : a = b;
  rw[if_pos hab,if_pos hab,hai]
  rw[if_neg hab,hai]
· simp[hai,Matrix.updateRow_apply]
  by_cases haj : a = j;
  rw[if_pos haj,if_pos haj,hai]
  rw[if_neg haj,hai]
· simp[Matrix.updateRow_apply]
  by_cases haj : a = j;
  · rw[if_pos haj,if_neg ,haj]
    exact Ne.trans_eq hai haj
  · simp[if_neg haj, if_neg (ne_comm.mp hai)]


--on multiplying by RowEx i j , the jth row becomes the ith row
theorem RowExmul_applyi_eq (M : Matrix n n R) (i j b : n) : (RowEx i j * M:) j b = M i b := by
rw[RowExmul_eq_swap]
simp[updateRow_apply]

--on multiplying by RowEx i j , the ith row becomes the jth row
theorem RowExmul_applyj_eq (M : Matrix n n R) (i j b : n) : (RowEx i j * M:) i b = M j b := by
rw[RowExmul_eq_swap]
simp[updateRow_apply]
intro h
rw[h]

--on multiplying by RowEx i j , if l ≠ j and l ≠ i then the lth row remains unchanged
theorem RowExmul_apply_ne (i j l b : n) (hi : i ≠ l) (hj : j ≠ l) (M : Matrix n n R): M l b = (RowEx i j * M:) l b :=by
simp[RowExmul_eq_swap,updateRow_apply]
simp[if_neg (id (Ne.symm hi)),if_neg (id (Ne.symm hj))]


--The determinant of RowEx i j when i ≠ j is -1
theorem RowEx_ne_det (i j : n)(h : i ≠ j): det (RowEx i j) = (-1 : R) := by
simp[RowEx,Matrix.det_permutation,Equiv.Perm.sign_swap,if_neg h]




namespace struct

open Sum Fin TransvectionStruct Pivot Matrix
variable (R n r)
--variable (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)

theorem rowExInl (M: Matrix (Fin r) (Fin r) 𝕜) (i j :Fin r) :
fromBlocks ((RowEx i j)*M) 0 0 (1: Matrix Unit Unit 𝕜) = (RowEx (inl i) (inl j))* (fromBlocks M 0 0 (1: Matrix Unit Unit 𝕜)) := by
ext a b
cases' a with a a <;> cases' b with b b
any_goals {simp[RowExmul_eq_swap,Matrix.updateRow_apply]}


theorem RowEx_InleqBlocks (i j : Fin r): fromBlocks (RowEx i j ) 0 0 (1: Matrix Unit Unit 𝕜) =
(RowEx (inl i) (inl j)) := by
suffices fromBlocks ((RowEx i j) * (1 : Matrix (Fin r) (Fin r) 𝕜)) 0 0 (1: Matrix Unit Unit 𝕜)=
(RowEx (inl i) (inl j)) * (1 : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) by simpa [Matrix.mul_one]
rw[rowExInl,Matrix.mul_one]
simp

structure elimStruct where
(L : List (TransvectionStruct n R))
(i j: n)

namespace elimStruct

variable {n R}
def toElim (e : elimStruct n R) : Matrix n n R :=
((e.L).map toMatrix).prod * (RowEx e.i e.j)



def elimSum_Inl (e : elimStruct n R ) : (elimStruct (n ⊕ p) R ) where
L := ((e.L).map (sumInl p))
i := inl e.i
j := inl e.j


theorem toMat_sumInl (e : elimStruct (Fin r) 𝕜) : (e.elimSum_Inl).toElim = fromBlocks e.toElim 0 0 (1 : Matrix Unit Unit 𝕜) := by
simp[toElim,elimSum_Inl,←RowEx_InleqBlocks ,sumInl_toMatrix_prod_mul]

theorem go (M : Matrix (Fin r) (Fin r) 𝕜) (L : List (elimStruct (Fin r) 𝕜)) (N : Matrix Unit Unit 𝕜) (O : Matrix Unit (Fin r) 𝕜):
(L.map (toElim ∘ elimSum_Inl)).prod * fromBlocks M (0: Matrix (Fin r) Unit 𝕜) O N =
fromBlocks ((L.map toElim).prod * M) (0: Matrix (Fin r) Unit 𝕜) O N := by
 induction' L with t L IH
 · simp
 · simp[Matrix.mul_assoc, IH, toMat_sumInl, fromBlocks_multiply]


--variable {p}

--list of transvections where c is zero


def listid(k:ℕ) : List (Matrix (Sum (Fin k) Unit) (Sum (Fin k) Unit) 𝕜) :=
  List.ofFn fun i : Fin k =>
    transvection (inl i) (inr Unit.unit) (0:𝕜)

--Product of listid is an identity matrix
theorem listid_prod_eq_id(r : ℕ) : (listid r).prod = (1 : (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) ) := by
simp[listid]



/- For every r+1 by r+1 matrix M ,there is a list of transvections and a rowEx matrix such that
 multiplying on the left with the RowEx and then the list of transvections will make
 M₍ᵢ,ᵣ₊₁₎ = 0 for every 1 ≤ i < r+1 -/

theorem transvec_RowEx_mul_lastcol (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
 ∃ i :Fin r ⊕ Unit, ∃ L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜), (∀ j : Fin r,
 ((L.map toMatrix).prod *(((RowEx i (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)) (inl j) (inr 1) = 0) := by
  by_cases hMne0: M (inr 1) (inr 1) ≠ 0
  --Case 1: Bottom-right entry is non-zero
  --Begin by creating the i and L that is required and inserting it in the goal
  ·let a : Fin r ⊕ Unit := inr 1 -- a = r+1
   use a
   let N : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜 := (((RowEx a (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M) -- the matrix obtained after exchanging the a-th row with the last row
   have hNM: N = M := by exact RowExid a M
   let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr 1, by simp, - N (inl i) (inr 1) / N (inr 1) (inr 1)⟩
   refine' ⟨L,_⟩
   intro j
   have hLN : L.map toMatrix = listTransvecCol N
   := by
        simp [L,hNM,transvection,listTransvecCol]
        rfl
   have h1: RowEx a (inr 1) * M = N := by rfl
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
      --if there is atleast one non-zero element in last column, you can make the M₍ᵣ₊₁,ᵣ₊₁₎ non-zero using RowEx
      · have hn : (((RowEx (inl i) (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) * M) (inr 1) (inr 1) ≠ 0) := by
         rw[RowExmul_eq_swap]
         rw[Matrix.updateRow_self]
         exact hi
         --Repeating a proof similar to Case 1 since M₍ᵣ₊₁,ᵣ₊₁₎ is non-zero
        let a : Fin r ⊕ Unit := inl i
        use a
        let N: Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜 := (((RowEx a (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)
        have h1: RowEx a (inr 1) * M = N := by rfl
        let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
         List.ofFn fun i : Fin r =>
           ⟨inl i, inr 1, by simp, - N (inl i) (inr 1) / N (inr 1) (inr 1)⟩
        refine' ⟨L,_⟩
        intro j
        have hLN : L.map toMatrix = listTransvecCol N := by
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
       List.ofFn fun i : Fin r =>
         ⟨inl i, inr 1, by simp, 0⟩
      use L
      intro j
      --have h1: ∀ i, (listid r)[i]? = (1: Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) := by
      have hL : L.map toMatrix = listid r := by
        refine List.map_eq_iff.mpr ?_
        intro i
        simp [listid,L,]
        exact List.getElem?_replicate
      rw[hL,listid_prod_eq_id,Matrix.one_mul,RowExii_eq_id,Matrix.one_mul]
      exact hexistsNon0 j

theorem exists_elimmatrix_mul_lastcol (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)  :
∃(N : elimStruct (Fin r ⊕ Unit) 𝕜), (∀ j : Fin r , ((N.toElim) * M) (inl j) (inr 1) = 0) :=by
 · have TH :  ∃ i :Fin r ⊕ Unit, ∃ L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜), (∀ j : Fin r,
   ((L.map toMatrix).prod *(((RowEx i (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)) (inl j) (inr 1) = 0):=by
    exact transvec_RowEx_mul_lastcol r M
   cases TH with
   |intro k TH =>
   cases TH with
   |intro L' TH =>
   simp[toElim]
   let N': elimStruct (Fin r ⊕ Unit) 𝕜 :=
   ⟨L',k,(inr 1)⟩
   exists N'
   simp[N']
   suffices  ∀ (j : Fin r),
   (List.prod (List.map toMatrix L') * ((RowEx k (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) * M)) (inl j) (inr 1)
    = 0 by
    simp[Matrix.mul_assoc]
    exact TH
   exact TH

end elimStruct

open elimStruct

theorem exists_Listelimmatrix_eq_lowertriangular (IH : ∀ (M : Matrix (Fin r) (Fin r) 𝕜), ∃ ( E :List (elimStruct (Fin r) 𝕜))
 , ((E.map toElim).prod * M).BlockTriangular OrderDual.toDual) (M :Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
  ∃ (E₁ : List (elimStruct (Fin r ⊕ Unit) 𝕜) ),
  ((E₁.map toElim).prod * M).BlockTriangular OrderDual.toDual := by
  have HM : ∃ N : elimStruct (Fin r ⊕ Unit) 𝕜, ∀ (j : Fin r), (toElim N * M) (inl j) (inr Unit.unit) = 0 := by
   exact exists_elimmatrix_mul_lastcol r M
  cases HM with
  |intro N HM =>
  let M' := N.toElim*M
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L, h₀⟩
  set Mₐ := toBlocks₂₁ M'
  set c := toBlocks₂₂ M'
  refine'⟨L.map (elimSum_Inl) ++ [N],_⟩
  suffices ((L.map (toElim ∘ elimSum_Inl)).prod * M').BlockTriangular OrderDual.toDual by simpa[Matrix.mul_assoc]
  have H : M' = fromBlocks (M'') 0 Mₐ c := by
    have X : toBlocks₁₂ (M') = 0 := by
      ext a b
      simp[toBlocks₁₂]
      exact HM a
    rw[←X]
    exact Eq.symm (fromBlocks_toBlocks M')
  rw[H,go]
  simpa[BlockTriangular]
