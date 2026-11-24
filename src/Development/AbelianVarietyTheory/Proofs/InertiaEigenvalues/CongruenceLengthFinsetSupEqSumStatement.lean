module

public import Mathlib.RingTheory.Length
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthFinsetSupEqSum
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
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

theorem _root_.GlobalTheory.T.congruenceLength_finset_sup_eq_sum : ∀ (O V ι : Type) [CommRing O] [AddCommGroup V] [Module O V] (F : Finset ι) (L G B : ι → Submodule O V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → (∀ i ∈ F, L i ≤ G i ⊔ B i) → Module.length O (↥(F.sup G ⊓ (F.sup L ⊔ F.sup B)) ⧸ (F.sup L ⊓ F.sup G).comap (F.sup G ⊓ (F.sup L ⊔ F.sup B)).subtype) = ∑ i ∈ F, Module.length O (↥(G i ⊓ (L i ⊔ B i)) ⧸ (L i ⊓ G i).comap (G i ⊓ (L i ⊔ B i)).subtype) := by
  first | exact @GlobalTheory.congruence_length_finset_sup | exact GlobalTheory.congruence_length_finset_sup | (intros; apply GlobalTheory.congruence_length_finset_sup <;> assumption)
