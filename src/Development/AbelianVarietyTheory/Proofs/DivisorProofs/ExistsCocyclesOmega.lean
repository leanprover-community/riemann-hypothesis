module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.exists_cocycles_omega : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
    ∃ (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ ∀ n, w.1 n = d.om n := by
  intro R _ A _ hA p G t c d
  have hs : IsSymCoc d.g := isSymCoc_of_isAdd R A hA _ _ d.add
  refine ⟨⟨fun n => d.coc n, fun n => ⟨coc_mem_symCocycles R A p G t c d hs n,
    Dat.pullTwo_res_coc R A p G t c d n⟩⟩, ⟨fun n => d.om n, fun n => OmRes.cotMap_res_om R A p G t c d n⟩,
    fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.PtExt
