module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OClsAt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.FiniteEtaleModels.O.baseOnto :
    UpperTheory.Gal.FiniteEtaleModels.BaseOnto := by
  intro p _ D G L hsc E _ _ gb w q _ r 𝔴 𝔫 S k T M c a hnum C Ω _ _ y σ hy
  have hComp : QComp := UpperTheory.quotient_map_comp
  have hCls : ClsEx := UpperTheory.isogeny_class_exists_of_quotient UpperTheory.quotient_moduli_object_exists UpperTheory.quotient_map_comp (UpperTheory.quotient_unique_of_comp UpperTheory.quotient_map_comp)
    (UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation)
  have hpos : 0 < M.1 := by
    have := M.2.1
    omega
  obtain ⟨o, C', hC'⟩ := UpperTheory.Gal.FiniteEtaleModels.O.clsAt q (datAt S.atq S.sp) hsc.m1 r S.atq.root (Ow w) E S.b gb
    (algebraMap (Ow w) E) S.mat M.1 S.N₀ c a S.𝔞 hnum.1 hpos S.std.cop hnum.2 S.upow S.Y Ω y σ hy
  obtain ⟨x, ⟨hxs, ⟨m⟩⟩, -⟩ := (T.M M).rep (Sp Ω) σ o
  obtain ⟨n', hn'⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb M.1 S.N₀ c _ _ _ (T.M M).s S.Y.s S.Y.s
    (T.M M).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2 (Sp Ω) σ o x m C.m
  have hov : (x ≫ C.j) ≫ S.Y.s = σ ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, ← Category.assoc, hxs]
  have hlv : ∀ v : (datAt S.atq S.sp).La,
      (o.eta (algebraMap (𝓞 (datAt S.atq S.sp).F) (datAt S.atq S.sp).O a • v)).left ≫ n'.φ =
        (x ≫ C.j) ≫ (S.Y.lv v).left := by
    intro v
    rw [hn', ← Category.assoc]
    refine (congrArg (· ≫ C.m.φ) (m.eta _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (x ≫ ·) (C.lv v)).trans ?_
    exact (Category.assoc _ _ _).symm
  have hu := (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M.1 S.N₀ c a S.𝔞 hnum.1 hpos
    S.std.three S.std.cop hnum.2 S.Y (Sp Ω) σ o).2 ⟨x ≫ C.j, hov, n', hlv⟩ C'
  exact ⟨x, hu.1.trans hC', hxs⟩
