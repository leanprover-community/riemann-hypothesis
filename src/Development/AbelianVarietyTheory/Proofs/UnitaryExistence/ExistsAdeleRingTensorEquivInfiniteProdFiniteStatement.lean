module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

theorem _root_.GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
    exact @GlobalTheory.AdSplit.exists_adele_equiv
