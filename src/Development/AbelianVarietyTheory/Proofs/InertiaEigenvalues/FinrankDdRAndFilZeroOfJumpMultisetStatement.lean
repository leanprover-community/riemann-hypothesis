module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultiset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  first | exact @GlobalTheory.JumpDims.dims_of_mult | exact GlobalTheory.JumpDims.dims_of_mult | (intros; apply GlobalTheory.JumpDims.dims_of_mult <;> assumption)
