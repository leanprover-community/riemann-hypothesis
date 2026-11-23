module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EigenFrames
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.LB (resG_resG le_iSup_inf)

variable {X : Scheme.{0}} {F G : X.Modules}

theorem isFrame_mkSec (N : Sub F) {U : X.Opens} {ν : Type} [Fintype ν] (e : ν → Γ(F, U))
    (he : ∀ i, e i ∈ N.sec U)
    (hli : ∀ (V : X.Opens) (h : V ≤ U), LinearIndependent Γ(X, V) fun i => resM F h (e i))
    (hsp : ∀ (V : X.Opens) (h : V ≤ U) (x : Γ(F, V)), x ∈ N.sec V →
      x ∈ Submodule.span Γ(X, V) (Set.range fun i => resM F h (e i))) :
    GlobalTheory.VB.IsFrame (F := N.toMod) fun i => N.mkSec (e i) (he i) := by
  rw [GlobalTheory.VB.isFrame_iff]
  intro V h
  have hcomp : (appLinear N.incl V) ∘ (fun i => resM N.toMod h (N.mkSec (e i) (he i))) =
      fun i => resM F h (e i) := funext fun i => by
    simp only [Function.comp, appLinear_apply]
    rw [app_resM]
    rfl
  refine ⟨LinearIndependent.of_comp (appLinear N.incl V) (hcomp ▸ hli V h), ?_⟩
  rintro y -
  have hx := hsp V h _ (N.incl_app_mem y)
  rw [← hcomp, Set.range_comp, Submodule.span_image] at hx
  obtain ⟨y', hy', e'⟩ := hx
  have : y' = y := N.incl_app_injective V (by rwa [appLinear_apply] at e')
  exact this ▸ hy'


variable {O : Type} [CommRing O] (ρ : O →+* CategoryTheory.End F) {κ : Type} [Fintype κ]
  (τ : κ → (O →+* Γ(X, ⊤))) {m : κ → ℕ} {U : X.Opens} (B : (Σ i, Fin (m i)) → Γ(F, U))
  (hB : GlobalTheory.VB.IsFrame B)
  (hact : ∀ i k a, (act ρ a).app U (B ⟨i, k⟩) = resG X (le_top : U ≤ ⊤) (τ i a) • B ⟨i, k⟩)


end GlobalTheory.EigenFrames
