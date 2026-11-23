module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrime
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.traceCombination_coverForm_integral_over_prime : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  first | exact @GlobalTheory.TraceIdem.trace_comb_integral | exact GlobalTheory.TraceIdem.trace_comb_integral | (intros; apply GlobalTheory.TraceIdem.trace_comb_integral <;> assumption)
