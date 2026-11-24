module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

theorem _root_.GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.ModelOfOutput.exists_zOn | exact GlobalTheory.ModelOfOutput.exists_zOn | (intros; apply GlobalTheory.ModelOfOutput.exists_zOn <;> assumption)
