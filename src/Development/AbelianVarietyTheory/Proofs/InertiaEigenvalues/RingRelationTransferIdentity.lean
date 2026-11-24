module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnivCharCopy

theorem ring_relation_transfer_identity {R R' : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {H' : Formalism.BasicNotions.Host R'} {Ω Ω' : Type}
    [iΩ : Field Ω] [iΩ' : Field Ω'] [aΩ : Algebra H.E Ω] [aΩ' : Algebra H'.E Ω'] {T T' : Type}
    {cc : Ω ≃+* Ω} {cc' : Ω' ≃+* Ω'} {l : T → ℕ} {l' : T' → ℕ}
    {d : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E Ω →* Multiplicative (DelQM H (l i) Q M)}
    {d' : ∀ i (Q : Finset (PlE H')) (M : ℕ), G H'.E Ω' →* Multiplicative (DelQM H' (l' i) Q M)}
    (hR : R = R') (hH : HEq H H') (hΩ : Ω = Ω') (hi : HEq iΩ iΩ') (ha : HEq aΩ aΩ') (hcc : HEq cc cc')
    (hT : T = T') (hl : HEq l l') (hd : HEq d d')
    (h : ∀ i Q M, d i Q M = GlobalTheory.GalChar.delU H cc (l i) Q M) :
    ∀ i Q M, d' i Q M = GlobalTheory.GalChar.delU H' cc' (l' i) Q M := by
  subst hR; cases hH; subst hΩ; cases hi; cases ha; cases hcc; subst hT; cases hl; cases hd
  exact h

theorem isUnivChar_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e), GlobalTheory.UnivChar.IsUnivChar D.nexp → GlobalTheory.UnivChar.IsUnivChar D'.nexp := by
  intro D D' ι e h hU
  exact ring_relation_transfer_identity h.gal.R h.gal.host (eq_of_heq h.gal.Om) h.gal.instOm h.gal.algOm h.set.cc
    (eq_of_heq h.set.Tw) h.set.l h.delU hU

end GlobalTheory.UnivCharCopy

end
