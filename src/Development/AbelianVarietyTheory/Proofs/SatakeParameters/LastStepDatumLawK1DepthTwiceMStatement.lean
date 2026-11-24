module

public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.twTt_k1Depth_twice_m : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ} (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)) (hc' : κ'⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H) (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))), R.m = m2 + 2 → cst.Ok → ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → 2 * cst.M ≤ cst.D w → 2 * cst.M ≤ twTopDepth R → ((qOf w.1 : X.E) ^ cst.M) • y₁ ∈ stdAt X.E (R.N (m2 + 1)) w.1 → rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) * topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y) y₁ = (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) * topDat Ch sel mu cst (m2 + 1) w y y₁ := by
  first | exact @GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | exact GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | (intros; apply GlobalTheory.lastStepDatumLaw_K1Depth_twiceM <;> assumption)
