module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingAllHeckeEigenvalue
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

theorem _root_.GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂), (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) → ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k → ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  first | exact @GlobalTheory.HeckeSplitField.exists_finExt_split | exact GlobalTheory.HeckeSplitField.exists_finExt_split | (intros; apply GlobalTheory.HeckeSplitField.exists_finExt_split <;> assumption)
