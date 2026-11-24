module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

abbrev XQ (X : Scheme.{0}) : Scheme.{0} := pullback (toZ X) (toZ (Sp ℚ))

abbrev XQ.fst (X : Scheme.{0}) : XQ X ⟶ X := pullback.fst _ _

abbrev XQ.snd (X : Scheme.{0}) : XQ X ⟶ Sp ℚ := pullback.snd _ _

def toXQ {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) : Sp F ⟶ XQ X :=
  pullback.lift x (spMap (algebraMap ℚ F)) (specULiftZIsTerminal.hom_ext _ _)

@[simp] theorem toXQ_fst {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) :
    toXQ x ≫ XQ.fst X = x := pullback.lift_fst _ _ _

def evalAt {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) : ℂ :=
  (Scheme.stalkClosedPointTo z).hom (S.presheaf.germ U (centre z) hz f)

def anTop (S : Scheme.{0}) : TopologicalSpace (Sp ℂ ⟶ S) :=
  TopologicalSpace.generateFrom
    {A | ∃ (U : S.Opens) (f : Γ(S, U)) (V : Set ℂ), IsOpen V ∧ A = {z | ∃ hz : centre z ∈ U, evalAt U f z hz ∈ V}}

section Good

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li}

def GoodAt (h : LieMetric M y) (C : ℝ) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) {GK : Over (Sp L)}
    [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) : Prop :=
  letI := τ.addCommGroup
  ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)),
    ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT →
    ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier),
      IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier,
      (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) →
      ∀ (σ : L →+* ℂ) (w : Fin r → ℂ),
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧
        sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2

end Good

end GlobalTheory.CompanionTheory.Ar.TorusUnif
