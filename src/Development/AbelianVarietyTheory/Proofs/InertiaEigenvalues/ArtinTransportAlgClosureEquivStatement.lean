module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTransportAlgClosureEquiv
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.artin_transport_algClosure_equiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E'] (φ : Ω ≃+* Ω'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x)) → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω), (∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ) → ∀ (B : Type) [CommGroup B] (χ : GlobalTheory.HeckeGal.Gab E Ω →* B) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')), w.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = v.asIdeal → (∀ x, Formalism.L2.Host.IsUnitAt v x → χ (art (Neutral.B1.localIdele E v x)) = 1) → (∀ x, Formalism.L2.Host.IsUnitAt w x → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = 1) ∧ ∀ x ϖ, Formalism.L2.Host.IsUnifAt w x → Formalism.L2.Host.IsUnifAt v ϖ → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = χ (art (Neutral.B1.localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
  first | exact @GlobalTheory.ArtinTransport.chi_artin_transport | exact GlobalTheory.ArtinTransport.chi_artin_transport | (intros; apply GlobalTheory.ArtinTransport.chi_artin_transport <;> assumption)
