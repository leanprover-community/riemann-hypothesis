import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.SqfCounts

section
noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

def kF (c : ℝ) : ℝ := (1 + Real.exp (-(c * Real.log 6))) / (1 - Real.exp (-(c * Real.log 6)))

theorem exp_neg_log_six_lt_one {c : ℝ} (hc : 0 < c) : Real.exp (-(c * Real.log 6)) < 1 := by
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

theorem kF_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ kF c := by
  have h := exp_neg_log_six_lt_one hc
  have h0 := Real.exp_pos (-(c * Real.log 6))
  unfold kF
  exact div_nonneg (by linarith) (by linarith)


theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]


end Formalism.MainNotions.FamilyNumericLemmas
end
end

section
noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology Polynomial

structure AllRowsAt (D : D7) (Dall Dgood : ℕ) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin Dgood → Fin Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D : D7} {Dall Dgood : ℕ}

def AllRowsAt.dimT (A : AllRowsAt D Dall Dgood) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def LabelCountSpace (A : AllRowsAt D Dall Dgood) : Prop :=
  (∀ S : Set (Tup2 D), A.dimT S = Nat.card {τ : Fin Dall // (fun k => A.labAll k τ) ∈ S}) ∧
    Function.Injective A.inc ∧
    ∀ τ : Fin Dall, D.ntypes.goodTuple (fun k => A.labAll k τ) ↔ τ ∈ Set.range A.inc

def TieCountAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def Adm2At (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) : Prop :=
  adm1 D n₀ Alev C₃ c₃ cb ∧ lawL D A.eVec CL ∧ LabelCountSpace A ∧ TieCountAt A n₀ Alev C₃ cb ∧ TieAdmG D

def DeficitBracketBound (Dall Dgood : ℕ) (C c o : ℝ) : Prop :=
  (Dall : ℝ) - (Dgood : ℝ) ≤ C * br2 D c o * (Dall : ℝ)

def ExpDeficitBound' (Dall Dgood : ℕ) (x eps : ℝ) : Prop :=
  (Dall : ℝ) - (Dgood : ℝ) ≤ Real.exp (-(x ^ (eps / 7))) * (Dall : ℝ)

def FamilyDeficitBracketBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∃ o : ℝ → ℝ, Tendsto o atTop (𝓝 0) ∧
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (ι : J x i), DeficitBracketBound (Fm.D x i) (Dall x i ι) (Dgood x i ι) C c (o x)

def FamilyExpDeficitBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (ι : J x i), ExpDeficitBound' (Dall x i ι) (Dgood x i ι) x Fm.ez

def FamilyDeficitTheorem {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : Prop :=
  ∀ (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ), 0 < c₃ →
    (∀ x ≥ x₂, ∀ (i : Fm.Ix x) (ι : J x i), Adm2At (Fm.D x i) (A x i ι) n₀ Alev C₃ c₃ cb CL) → ParO Fm →
      FamilyDeficitBracketBound Fm J Dall Dgood ∧ (ParX Fm → FamilyExpDeficitBound Fm J Dall Dgood)

def AllRows.toAt {D : D7} (A : AllRows D) : AllRowsAt D D.what₂.Dall D.what₂.Drows where
  B := A.B
  n_eq := A.n_eq
  f_eq := A.f_eq
  labAll := A.labAll
  labAll_label := A.labAll_label
  inc := A.inc
  eVec := A.eVec
  eVec_idem := A.eVec_idem
  eT := A.eT
  ReT := A.ReT
  ReT_spec := A.ReT_spec
  eT_univ := A.eT_univ
  ReT_univ := A.ReT_univ
  eT_one := A.eT_one



end Formalism.MainNotions.ArithmeticCylinders

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial


def LocU {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) {Dall Dgood : ∀ x i, J x i → ℕ}
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : Prop :=
  ∀ CL x₂ : ℝ,
    (∀ x ≥ x₂, ∀ (i : Fm.Ix x) (ι : J x i), lawL (Fm.D x i) (A x i ι).eVec CL ∧ TieAdmG (Fm.D x i)) → ParO Fm →
      ∃ C c : ℝ, 0 < c ∧ ∃ o : ℝ → ℝ, Tendsto o atTop (𝓝 0) ∧
        ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (ι : J x i), LocalShareBound (Fm.D x i) (A x i ι).eVec C c (o x)






end Formalism.MainNotions.N.CylinderCountFamily
end
end
