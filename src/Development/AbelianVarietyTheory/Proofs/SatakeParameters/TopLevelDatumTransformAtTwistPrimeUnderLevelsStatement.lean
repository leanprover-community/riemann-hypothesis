module

public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.KernelLattices.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevels
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ},
  ChIdx.Ok Ch sel mu cst L G m2 → QUnif sel mu → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∀ (g' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z' : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g' z' →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))),
  ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y₁ - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  ((qOf P.1 : X.E) ^ cst.M) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  z' * topDat Ch sel mu cst (m2 + 1) P (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) (g.symm y₁) *
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) =
    z * topDat Ch sel mu cst (m2 + 1) P y y₂ := by
  first | exact @GlobalTheory.TwTopLaw.topLawQ_midTop | exact GlobalTheory.TwTopLaw.topLawQ_midTop | (intros; apply GlobalTheory.TwTopLaw.topLawQ_midTop <;> assumption)
