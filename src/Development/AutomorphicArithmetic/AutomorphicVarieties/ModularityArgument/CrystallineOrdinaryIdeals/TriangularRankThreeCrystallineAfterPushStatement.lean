module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPush
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.triangular_rank_three_crystalline_after_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  exact @GlobalTheory.tri_crys_push
