module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBot
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG (m := 3) (R := B)), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  exact @GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot
