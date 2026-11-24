module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  first | exact @GlobalTheory.CuspRep.CompUniq.isotypic | exact GlobalTheory.CuspRep.CompUniq.isotypic | (intros; apply GlobalTheory.CuspRep.CompUniq.isotypic <;> assumption)
