module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.offEx_holds :
    UpperTheory.Gal.KunnethLefschetz.OffEx := by
  refine ⟨fun {Z X} ι hι => ⟨⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩, rfl⟩, ?_⟩
  intro Z' X' Z X ι' ι f u h U hU
  change f ⁻¹' (U : Set X) = _
  rw [hU, Set.preimage_compl, ← Scheme.Pullback.range_fst]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
