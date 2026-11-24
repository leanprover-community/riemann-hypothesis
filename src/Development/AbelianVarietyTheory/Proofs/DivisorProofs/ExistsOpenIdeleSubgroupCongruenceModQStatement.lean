module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  first | exact @GlobalTheory.OpenCongrIdele.exists_open_congr | exact GlobalTheory.OpenCongrIdele.exists_open_congr | (intros; apply GlobalTheory.OpenCongrIdele.exists_open_congr <;> assumption)
