module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Support
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientSpanIffOfIsPushout
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' : ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'), IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'), ((letI := qa'.hom.toAlgebra; p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔ (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first | (exact @GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (exact GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (intros; apply GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout  <;> assumption)
