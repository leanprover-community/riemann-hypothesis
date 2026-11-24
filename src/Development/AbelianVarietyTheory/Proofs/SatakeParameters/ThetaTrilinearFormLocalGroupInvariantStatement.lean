module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaTrilinearFormLocalGroupInvariant
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

theorem _root_.GlobalTheory.T.thetaTrilinearForm_localGroup_invariant : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) (Θ : ThetaMod D M i X μ η) (s : SplitPlace D.host.E) (μw ηw : (s.w.adicCompletion D.host.E)ˣ →* ℂˣ) (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Θ.Ω) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r), TrivOutside {s.v} h → TrivOutside {s.v} g → ∀ Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h)) Φ → Θ.ω (h, g) (ι Φ) = ((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h))) : ℂˣ) : ℂ) • ι Φ') → ∀ (Wl Vl : Type) [AddCommGroup Wl] [Module ℂ Wl] [AddCommGroup Vl] [Module ℂ Vl] (πl : Representation ℂ (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) Wl) (σl : Representation ℂ (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) Vl) (T' : Wl →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)), (∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (πl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (M.loc i).wt.W)) → ∀ (T'' : Vl →ₗ[ℂ] ↥X.C), (∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (σl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)) → ∀ (g : GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) (h : GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) (Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E))), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw g h Φ → ∀ a c', Θ.Λ (ι Φ') (T' (twist πl (detChar (Fin D.R.nV) ηw) h a)) (T'' (σl g c')) = Θ.Λ (ι Φ) (T' a) (T'' c') := by
  first | exact @GlobalTheory.ThetaLocInv.thetaRead_inv | exact GlobalTheory.ThetaLocInv.thetaRead_inv | (intros; apply GlobalTheory.ThetaLocInv.thetaRead_inv <;> assumption)
