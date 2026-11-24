module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.localisation_galoisCharacter_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  first | exact @GlobalTheory.HeckeLocCont.chiN_continuous | exact GlobalTheory.HeckeLocCont.chiN_continuous | (intros; apply GlobalTheory.HeckeLocCont.chiN_continuous <;> assumption)
