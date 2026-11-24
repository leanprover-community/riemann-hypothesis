module

public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrime
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'' := by
  intro X Pr R Ch sel S mu cst m2 hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact GlobalTheory.TopFrameQM.topDat_frames_qM Ch sel mu cst hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
