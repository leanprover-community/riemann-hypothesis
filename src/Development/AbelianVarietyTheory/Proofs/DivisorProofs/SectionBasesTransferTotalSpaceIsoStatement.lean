module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sectionBases_transfer_totalSpaceIso : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  first | (exact @GlobalTheory.SecBasisTransfer.bases_transfer) | (exact GlobalTheory.SecBasisTransfer.bases_transfer) | (intros; apply GlobalTheory.SecBasisTransfer.bases_transfer  <;> assumption)
