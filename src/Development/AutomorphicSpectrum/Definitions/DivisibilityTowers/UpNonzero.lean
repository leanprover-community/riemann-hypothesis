import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)

namespace GlobalTheory.CompanionTheory.OntoAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def NodeGap (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (j : Fin D.R.m) (h : j.1 + 1 < D.R.m),
    (D.R.t : ℚ) + 2 * ((D.R.r + D.R.m * D.R.t + 1 : ℕ) : ℚ) ^ 3 + 1 ≤ (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).b j

def rowsAll (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (MMap (R.MY 0)) :=
  Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P))

def partAll (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badPl R A.μ0) c

def reachedAll (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (partAll R c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R A.μ0 k u x}) k

def StepAll (c : EigSys D) (k : ℕ) (Λ : ℝ) : Prop :=
  ∀ u₁ ∈ reachedAll R c k, ∀ u₂ ∈ reachedAll R c k, ∀ x₁ x₂, IsUp R A.μ0 k u₁ x₁ → IsUp R A.μ0 k u₂ x₂ →
    ∃ a : ℂ, IsIP R A.μ0 k u₁ u₂ a ∧ IsIP R A.μ0 (k + 1) x₁ x₂ ((Λ : ℂ) * a)

def TopAll (c : EigSys D) (Λ : ℝ) : Prop :=
  ∀ u₁ ∈ reachedAll R c (D.R.m - 1), ∀ u₂ ∈ reachedAll R c (D.R.m - 1), ∀ x₁ x₂,
    IsUpTop R A.μ0 u₁ x₁ → IsUpTop R A.μ0 u₂ x₂ → ∃ a : ℂ, IsIP R A.μ0 (D.R.m - 1) u₁ u₂ a ∧ ⟪x₁, x₂⟫_ℂ = (Λ : ℂ) * a

def PosAll : Prop :=
  ∀ c : EigSys D, (∀ k, k + 1 < D.R.m → ∃ Λ : ℝ, 0 < Λ ∧ StepAll R c k Λ) ∧ ∃ Λ : ℝ, 0 < Λ ∧ TopAll R c Λ

def NonVanAll : Prop :=
  ∀ c : EigSys D, (∀ k, k + 1 < D.R.m → ∀ u ∈ reachedAll R c k, IsUp R A.μ0 k u 0 → u = 0) ∧
    ∀ u ∈ reachedAll R c (D.R.m - 1), IsUpTop R A.μ0 u 0 → u = 0

def ScalarsAll : Prop :=
  ∃ κ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < κ j) ∧ ∀ c : EigSys D, partAll R c ≠ ⊥ →
    ∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R A.μ0) D.R.r c B ∧
      (∀ k, k + 1 < D.R.m → ∃ l, IsLValue R A.μ0 B (k + 1) l ∧ StepAll R c k (κ (k + 1) * l)) ∧
      ∃ l, IsLValue R A.μ0 B D.R.m l ∧ TopAll R c (κ D.R.m * l)

def FinAll : Prop := ∀ k, k < D.R.m → FiniteDimensional ℂ (R.CC A.μ0 k)

def dn (y : (R.HX A.μ0).H) : MMap (R.MY 0) := PiTensorProduct.lift.symm (R.thDn A.μ0 y)

def MatchAll (P : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HX A.μ0).H, (R.HX A.μ0).e y' = GlobalTheory.Hk3.hkF D.sp.X' P cX ((R.HX A.μ0).e y) →
    dn R y' = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c0) (dn R y)

def OntoTriv : Prop := ∀ u ∈ rowsAll R R.triv, ∃ y, dn R y = u

def datXP (P : LevelP R.Pg D.R.r ℂ) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q A.μ0) P R.chi (R.xiR A.μ0) Frm.B

def HasLev (P : LevelP R.Pg D.R.r ℂ) (y : (R.HX A.μ0).H) : Prop :=
  ∀ v, ∀ k ∈ levS _ R.βX (datXP R P), ∀ g,
    R.cX.toMap R.prX ((R.HX A.μ0).e y) v (g * k) = levChi _ R.βX (datXP R P) k * R.cX.toMap R.prX ((R.HX A.μ0).e y) v g

def OntoLev (P : LevelP R.Pg D.R.r ℂ) : Prop := ∀ u ∈ rowsAll R P, ∃ y, HasLev R P y ∧ dn R y = u

def DnEquiv : Prop :=
  ∀ (g : G) (y y' : (R.HX A.μ0).H),
    (∀ v, R.cX.toMap R.prX ((R.HX A.μ0).e y') v =
      actL D.sp.X' R.βX (R.datXt A.μ0) (R.eG g) (R.cX.toMap R.prX ((R.HX A.μ0).e y) v)) →
    dn R y' = postOn (R.MY 0) (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (dn R y)

def OntoAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.Hk3.Core R F → NodeGap D → OntoLev R (R.levR F true)

end GlobalTheory.CompanionTheory.OntoAll

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)
open GlobalTheory.LFun (Fam twist segFam val above IsCont Bounded IsSysParamD)

namespace GlobalTheory.CompanionTheory.OntoAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def badE : Set (HeightOneSpectrum (𝓞 D.host.E)) := above D.host.E (badPl R A.μ0 : Set (HeightOneSpectrum (𝓞 D.host.F)))

def upFun (k : ℕ) (u : MMap (R.MY k)) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec) (h : GA D (Yc D (k + 1))) : ℂ :=
  ∫ g in R.fdY A.μ0 k, star (thetaKO (R.ωY A.μ0 k) g h (R.ptY A.μ0 k φ)) * u v g ∂(R.νY A.μ0 k)

def upFunX (u : MMap (R.MY (D.R.m - 1))) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec)
    (h : GA D D.sp.X') : ℂ :=
  ∫ g in R.fdY A.μ0 (D.R.m - 1), star (thetaKO (R.ωX A.μ0) g h (R.ptX A.μ0 φ)) * u v g ∂(R.νY A.μ0 (D.R.m - 1))

def partAt (k : ℕ) (c : EigSys D) : Submodule ℂ (MMap (R.MY k)) :=
  partDual R.θ (R.MY k) (levS _ (R.βY k) (R.datYt A.μ0 k R.triv)) (levChi _ (R.βY k) (R.datYt A.μ0 k R.triv)) (badPl R A.μ0) c

def chainPar (B : Fam D.host.E) (k : ℕ) : Fam D.host.E :=
  B + ∑ i ∈ Finset.range k, segFam (val (R.toLevCh.mu A.μ0 (i + 1))) D.R.t

def parK (B : Fam D.host.E) (k : ℕ) : Fam D.host.E :=
  if Even k then chainPar R B k else twist (chainPar R B k) (val R.eta)⁻¹

def stepPar (B : Fam D.host.E) (k : ℕ) : Fam D.host.E := twist (chainPar R B k) (val (R.toLevCh.mu A.μ0 (k + 1)))⁻¹

def TrivBd (B : Fam D.host.E) : Prop :=
  Bounded (badE R) B D.R.r (((D.R.r : ℝ) - 1) / 2) ∧ Bounded (badE R) (fun w => (B w).map (·⁻¹)) D.R.r (((D.R.r : ℝ) - 1) / 2)

def LGood (B : Fam D.host.E) (k : ℕ) : Prop :=
  ∃ (σ : ℝ) (Λ : ℂ → ℂ), σ < (1 + (D.R.t : ℝ)) / 2 ∧ IsCont (badE R) (stepPar R B k) σ Λ ∧ Λ ((1 + (D.R.t : ℂ)) / 2) ≠ 0

def NSInf (B : Fam D.host.E) (k : ℕ) : Prop :=
  {w : HeightOneSpectrum (𝓞 D.host.E) | w ∉ badE R ∧ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∧
    ∀ β ∈ stepPar R B k w, ∀ e ∈ ({((D.R.t : ℂ) - 1) / 2, -(((D.R.t : ℂ) - 1) / 2), ((D.R.t : ℂ) + 1) / 2, -(((D.R.t : ℂ) + 1) / 2)} : Set ℂ),
      (β : ℂ) ≠ GlobalTheory.LFun.npow w e}.Infinite

def ParAll : Prop :=
  ∀ c : EigSys D, partAll R c ≠ ⊥ → ∃ B, IsSysParamD D (badPl R A.μ0) D.R.r c B ∧ TrivBd R B

def StepPar : Prop :=
  ∀ (B : Fam D.host.E) (k : ℕ), k + 1 < D.R.m → ∀ (c : EigSys D), IsSysParamD D (badPl R A.μ0) (Yc D k).rank c (parK R B k) →
    ∀ u ∈ partAt R k c, ∀ x, IsUp R A.μ0 k u x → x ≠ 0 →
      ∃ c', x ∈ partAt R (k + 1) c' ∧ IsSysParamD D (badPl R A.μ0) (Yc D (k + 1)).rank c' (parK R B (k + 1))

def UpDetect : Prop :=
  (∀ k, k + 1 < D.R.m → ∀ u : MMap (R.MY k), PiTensorProduct.lift u ∈ R.CC A.μ0 k → IsUp R A.μ0 k u 0 →
    ∀ φ v h, upFun R k u φ v h = 0) ∧
  ∀ u : MMap (R.MY (D.R.m - 1)), PiTensorProduct.lift u ∈ R.CC A.μ0 (D.R.m - 1) → IsUpTop R A.μ0 u 0 →
    ∀ φ v h, upFunX R u φ v h = 0

def UpNonzero : Prop :=
  ∀ (B : Fam D.host.E) (c : EigSys D),
    (∀ k, k + 1 < D.R.m → IsSysParamD D (badPl R A.μ0) (Yc D k).rank c (parK R B k) → LGood R B k → NSInf R B k →
      ∀ u ∈ partAt R k c, u ≠ 0 → ∃ φ v h, upFun R k u φ v h ≠ 0) ∧
    (IsSysParamD D (badPl R A.μ0) (Yc D (D.R.m - 1)).rank c (parK R B (D.R.m - 1)) → LGood R B (D.R.m - 1) → NSInf R B (D.R.m - 1) →
      ∀ u ∈ partAt R (D.R.m - 1) c, u ≠ 0 → ∃ φ v h, upFunX R u φ v h ≠ 0)

end GlobalTheory.CompanionTheory.OntoAll

end
end
