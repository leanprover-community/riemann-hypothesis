module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
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

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal

theorem _root_.GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E) (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' → RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) → ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  first | exact @GlobalTheory.EtaleCompletionLift.exists_extension | exact GlobalTheory.EtaleCompletionLift.exists_extension | (intros; apply GlobalTheory.EtaleCompletionLift.exists_extension <;> assumption)
