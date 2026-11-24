module

public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace Formalism.L2.JoinChr

open Formalism.L2.Theta Formalism.L2.Host

structure SameChr {D : D7} {X : ThetaX D} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : ThetaTied D X) (H : ThetaChrTied D C nch Tp X) : Prop where

  idem : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e, IsPlIdem D e P

  fin : ∀ (c : X.Chr) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P →
    ∀ (k : D.host.Eˣ) (x : (AE D)ˣ), (x : AE D) = locE D e (k : D.host.E) →
      ((T.eChr c x : Circle) : ℂ) = (((H.eChr c).locK P k : ℂˣ) : ℂ)

  inf : ∀ θ, IsInfFam (D := D) θ → ∀ (c : X.Chr) (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : (AE D)ˣ),
    IsInfLoc D θ τ (k : D.host.E) (x : AE D) →
      ((T.eChr c x : Circle) : ℂ) = (((H.eChr c).locInf (plOf D θ τ) (atInf (plOf D θ τ) k) : ℂˣ) : ℂ)

end Formalism.L2.JoinChr

end
