module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransferStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem univ_map : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (A : Type) [CommRing A] [Algebra (X.O0 i) A] (π : B →ₐ[X.O0 i] A) (κ : GE N →* Bˣ) (κ' : GE N →* Aˣ), (∀ g, ((κ' g : Aˣ) : A) = π (κ g : Bˣ)) → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → Univ bkP i s κ' Q (Φ.map π) (fun g => (Z g).map π) := by
  intro D N X bkP i s B _ _ A _ _ π κ κ' hκ Q a Φ Z hU Y _ _ _ _
  letI : Module B Y := Module.compHom Y π.toRingHom
  have hsm : ∀ (b : B) (y : Y), b • y = π b • y := fun _ _ => rfl
  obtain ⟨hrep, hsel⟩ := GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s B A π κ κ' hκ Y hsm
  obtain ⟨h1, h2, h3⟩ := hU Y
  have hm : ∀ x : Fin a → Y, matAct (Φ.map π) x = matAct Φ x := fun _ => rfl
  have hr : ∀ g (x : Fin a → Y), rect ((Z g).map π) x = rect (Z g) x := fun _ _ => rfl
  have hc : ∀ f, Cob (repOn (Tgl i s) κ Y) f ↔ Cob (repOn (Tgl i s) κ' Y) f := fun f => by
    simp only [Cob, hrep]
  simp only [hm, hr]
  refine ⟨fun x hx => (hsel _ _).1 (h1 x hx), fun x hx hb => h2 x hx ((hc _).2 hb), fun f hf => ?_⟩
  obtain ⟨x, hx, hb⟩ := h3 f ((hsel _ _).2 hf)
  exact ⟨x, hx, (hc _).1 hb⟩

end GlobalTheory.NewPrime
