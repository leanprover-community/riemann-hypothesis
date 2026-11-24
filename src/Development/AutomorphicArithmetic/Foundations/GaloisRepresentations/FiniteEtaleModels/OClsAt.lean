module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevGrp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevExistsPull
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftSys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OOResim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ORaise
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

private lemma nat_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h'] at hN
  exact (Ideal.mul_le_right : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞) hN

theorem clsAt : ClsAt := by
  intro q _ D hm1 r hr R R' _ _ _ b gb β hmatch N N₀ c a 𝔞 hN hpos hcop hgen hue Y Ω _ _ y σ hyσ
  obtain ⟨o1, ⟨n1⟩⟩ := raise q D R R' b gb β hmatch N N₀ c hN hpos hcop Y.X Y.s Y.univ Ω y σ hyσ
  obtain ⟨o₀, ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull q D R b N₀ Y.X (Sp Ω) Y.s y Y.univ
  have htr : ∀ {f f' : Sp Ω ⟶ Y.X} (_ : f = f') (n : QMap o1 Y.univ f c),
      ∃ n'' : QMap o1 Y.univ f' c, n''.φ = n.φ := by
    intro f f' h n
    subst h
    exact ⟨n, rfl⟩
  obtain ⟨n1', hn1'⟩ := htr (Category.id_comp y).symm n1
  obtain ⟨n, hn⟩ := (UpperTheory.quotient_map_comp q D R R' b gb N N₀ c (Sp Ω) (Sp Ω) Y.X σ (y ≫ Y.s) Y.s o1 o₀ Y.univ
    (𝟙 _) y).2.1 n1' m
  rw [hn1'] at hn
  obtain ⟨l, hl, hln⟩ := UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation q D R R' b gb N N₀ c a 𝔞 hpos hgen (Sp Ω) σ (y ≫ Y.s) o1 o₀ n
  obtain ⟨lv', hlv', hlvm⟩ := isEtLev_exists_pull m Y.isLev
  obtain ⟨g₀, hg₀⟩ := Cmp.exists_levGrp hlv' hl
  obtain ⟨g, glin, gonto, ginj, giso, gtow, gN₀, gq⟩ := liftSys q D hm1 r hr 𝔞 N₀ hue hcop g₀
  obtain ⟨o', n', ho'⟩ := oResim q D R R' b gb N N₀ c hN hpos (Sp Ω) Y.X σ Y.s o1 Y.univ y n1 g
    ⟨glin, gonto, ginj, giso, gtow⟩ gN₀
  refine ⟨o', ⟨y, hyσ, n', fun y' => ?_⟩, rfl⟩
  have heta : o1.eta (g N (algebraMap (𝓞 D.F) D.O a • y')) = o1.eta (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y') := by
    obtain ⟨z1, hz1⟩ := glin N hpos (algebraMap (𝓞 D.F) D.O a) y'
    have hq := gq N hpos (nat_mem_of_isGen hgen) y'
    have hdiff : g N y' - liftAct g₀ y' ∈ wSub D 𝔞 1 := by
      rw [← Submodule.Quotient.eq]
      rw [mk_liftAct]
      exact hq
    obtain ⟨z2, hz2⟩ := ((UpperTheory.lattice_generation q D a N 𝔞 hpos hgen).1 _).mpr hdiff
    have hsplit : algebraMap (𝓞 D.F) D.O a • g N y' =
        algebraMap (𝓞 D.F) D.O a • liftAct g₀ y' + N • z2 := by
      rw [← hz2, ← smul_add]
      congr 1
      abel
    rw [hz1, hsplit]
    have e1 := o1.eta_add (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y' + N • z2) (N • z1)
    have e2 := o1.eta_add (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y') (N • z2)
    have k1 : o1.eta (N • z1) = 1 := o1.eta_ker z1
    have k2 : o1.eta (N • z2) = 1 := o1.eta_ker z2
    rw [k1, _root_.mul_one] at e1
    rw [k2, _root_.mul_one] at e2
    exact e1.trans e2
  rw [ho', heta, ← hlvm, hg₀, ← hln, Category.assoc, ← hn]

end UpperTheory.Gal.FiniteEtaleModels.O
