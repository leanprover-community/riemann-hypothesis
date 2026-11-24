module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.root_extension_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (X : RootExt l 𝓛.D 𝓛.t) (θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj), n ≠ 0 → (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → ∃ e : X.E →+* 𝒯.A.Acr n, Function.Bijective e ∧ (∀ z, e (algebraMap 𝓛.D X.E z) = θ.φ z) ∧ ∀ j m, e (X.r j m) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j m : 𝒯.A.A)) := by
  first | exact @GlobalTheory.CompanionTheory.TowerAcr.tower_acr | exact GlobalTheory.CompanionTheory.TowerAcr.tower_acr | (intros; apply GlobalTheory.CompanionTheory.TowerAcr.tower_acr <;> assumption)
