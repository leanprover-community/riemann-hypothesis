module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.rayClassFieldHostConductor_isRayClassField : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  first | exact @GlobalTheory.ParRayMax.rayField_isRay | exact GlobalTheory.ParRayMax.rayField_isRay | (intros; apply GlobalTheory.ParRayMax.rayField_isRay <;> assumption)
