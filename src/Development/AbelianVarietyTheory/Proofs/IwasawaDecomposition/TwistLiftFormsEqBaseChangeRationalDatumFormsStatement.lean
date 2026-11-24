module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumForms
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.formsExport_eq | exact GlobalTheory.HeightCounting.FormsStep.formsExport_eq | (intros; apply GlobalTheory.HeightCounting.FormsStep.formsExport_eq <;> assumption)
