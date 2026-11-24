module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfBlochKatoLiftingFamilyAtPlace
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.liftAll_of_blochKatoLiftingFamilyAtPlace : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (e : ℕ), LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) → ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)), BlochKatoDuality.LiftAll (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst) (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) e := by
  first | exact @GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW | exact GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW | (intros; apply GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW <;> assumption)
