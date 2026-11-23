module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.isometry_matching_lattices_matches_spherical_ops : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (β' : GL (Fin V'.rank) (Lev.EAf D)) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (Lev.EAf D)) (Φ : GfC V ≃ₜ* GfC V') (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N N' : ℕ), IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → GlobalTheory.CuspMult.IsFinIso V V' β β' Pg j Φ → ∀ (P : Pl D.host.E), ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (d : List ℤ) (B : Finset (GfC V)), GlobalTheory.Hk3.SphOp V P d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ GlobalTheory.Hk3.SphOp V' P d ((B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  first | exact @GlobalTheory.SphTrans.sphOp_iff | exact GlobalTheory.SphTrans.sphOp_iff | (intros; apply GlobalTheory.SphTrans.sphOp_iff <;> assumption)
