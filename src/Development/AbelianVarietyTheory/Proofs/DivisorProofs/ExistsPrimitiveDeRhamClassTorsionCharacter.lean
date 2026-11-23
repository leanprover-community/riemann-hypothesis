module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatOfIsAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatPowEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAddChiEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacterStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_dat_chi_eq (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (N : ℕ) (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ (p ^ N) : Pt A D) = 1 → GlobalTheory.PtExt.chi (p ^ N) d.g D x = b D x := by
  have : IsCommMonObj A := hA.comm
  have hn : ((p ^ N : ℕ) : R) = 0 := by
    simpa only [Nat.cast_pow] using hN
  have hR : GlobalTheory.PtExt.HasRoots A (p ^ N) := fun D _ _ x ↦
    GlobalTheory.PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) (pow_pos (Fact.out : p.Prime).pos N) D x
  obtain ⟨u, g, hu, hg, hchi⟩ := GlobalTheory.T.exists_pushout_torsor_nTorsion_character R A (p ^ N) hn hR b hb
  obtain ⟨f, hf⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective R A hs u hu
  obtain ⟨g', hg', hchi'⟩ := GlobalTheory.CobChi.exists_isAdd_chi_eq R A (p ^ N) hn u (fv f) g hg hf
  let c : primDR A := ⟨H1.mk _ f, by rw [show primDR A = ⊤ from hP]; exact Submodule.mem_top⟩
  obtain ⟨d, -, hd⟩ := GlobalTheory.PtExt.exists_dat_of_isAdd R A p G t c f rfl g' hg'
  refine ⟨c, d, fun D _ _ x hx ↦ ?_⟩
  rw [hd, hchi' D x hx, hchi D x hx]
