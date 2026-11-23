module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MArtinTr
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.conjugate_places_completion_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  first | exact @_root_.GlobalTheory.LocLanglands.artin_transport_m_alt | exact _root_.GlobalTheory.LocLanglands.artin_transport_m_alt | (intros; apply _root_.GlobalTheory.LocLanglands.artin_transport_m_alt <;> assumption)
end
