module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondOfEigenbasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem tripleSt_of_laws : Laws → ThetaUnifAV → TripleSt := by
  intro laws hθ E _ _ _ H D La _ _ EF g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  letI := H.starRing
  obtain ⟨D', e, -, -, hEF⟩ := PeriodDatum.exists_datum E H La EF D.p D.q g ty P Hm hty hbij hadj hlin hinj hdisc hspan
    hH hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp e.toAddEquiv.toAddMonoidHom
  have hP' : ∀ a, P' a = P (e a) := fun _ => rfl
  have hr : P'.range = P.range := by
    ext z
    exact ⟨fun ⟨a, h⟩ => ⟨e a, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by rw [hP', e.apply_symm_apply, h]⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hinj.comp e.injective, by rw [hr]; exact hdisc, ?_, Hm, hH, hpos, fun x y => ?_⟩
    · rw [hP', hP', map_smul, hlin]
    · rw [← hspan]; exact congrArg _ (congrArg SetLike.coe hr)
    · rw [hP', hP', him, hEF]
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    PeriodPoint.exists_triple laws Moduli.cube_of_isLB principalTorus_algebraic (exists_isMonHom_of_map_lattice hθ laws)
      (lbIso_cubeLB_of_pairing_adjoint laws) (PrimNorm.exists_primitive_normalisation laws.globalFns)
      (kTriv_of_descent laws) relAmple_finite_pow_iso D' ty P' hper
  let Q : PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  let oa : Q.OAct (𝓞 E) :=
    { T.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨r, hr⟩ := NormRos.exists_gen_rosati T.PP.isLB _ _ (T.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hr _⟩⟩ }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hdet : DetCond D T.act (spMap (RingHom.id ℂ)) H.rt0 :=
    PeriodPoint.detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
      (fun i a => heig _ _ (T.act.hom a) (hact a) i) (RingHom.id ℂ)
  rw [show spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) from Spec.map_id _] at hdet
  refine ⟨Q, oa, L, u, rfl, T.prim, hdet, ht₁, ht₂, fun z => hr ▸ hker z, hact, fun k a b c hk hc => ?_⟩
  have := hW k (e.symm a) (e.symm b) c hk (by rw [hEF, e.apply_symm_apply, e.apply_symm_apply, hc])
  rwa [hP', hP', e.apply_symm_apply, e.apply_symm_apply] at this

end GlobalTheory.Ex.Arch
end
