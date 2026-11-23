module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowBC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowOfBl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.OKDvr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ProjProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SubstXZero
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.IsCovPr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

theorem UpperTheory.Gal.KunnethLefschetz.G.sqCore (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (M : Model l K) (d : ℕ) (hM : M.Sm) (hd : SmoothOfRelativeDimension (d + 1) M.p) : ∃ S : Sq M (d + 1), Etale S.D.f := by
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  haveI : IsNoetherianRing (OK l K) := oKDvr l K
  let Z : Sch (OK l K) := Over.mk M.p
  haveI : SmoothOfRelativeDimension (d + 1) Z.hom := hd
  obtain ⟨W, π, hbl, hXp, hWp, -, hXs, hWs, -⟩ := blTop (OK l K) Z d hproj
  haveI : IsProper Z.hom := ((projProd (OK l K) Z.hom Z.hom hproj).2.2)
  obtain ⟨D, het, ⟨B⟩⟩ := blowOfBl (OK l K) (d + 1) π hbl
  let P : Model l K := ⟨(XX Z).left, (XX Z).hom⟩
  let Y : Model l K := ⟨W.left, W.hom⟩
  have hΔ : (dg Z).left ≫ P.p = M.p := Over.w (dg Z)
  have hπ : π.left ≫ P.p = Y.p := Over.w π
  haveI : Smooth P.p := SmoothOfRelativeDimension.smooth (d + 1 + (d + 1)) P.p
  haveI : Smooth Y.p := SmoothOfRelativeDimension.smooth (d + 1 + (d + 1)) Y.p
  have hP : P.Sm := ⟨⟨hXp, ϖ, hϖ, smSst _ ϖ P.p⟩, inferInstance⟩
  have hY : Y.Sm := ⟨⟨hWp, ϖ, hϖ, smSst _ ϖ Y.p⟩, inferInstance⟩
  have sq₀ : IsPullback (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) P.q P.p
      (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := IsPullback.of_hasPullback _ _
  have sqΔ : IsPullback (pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
      (Model.genMap (M := M) (N := P) (dg Z).left hΔ) (dg Z).left
      (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm sq₀
    rw [Model.genMap_q, hΔ]
    exact IsPullback.of_hasPullback _ _
  have sqπ : IsPullback (pullback.fst Y.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
      (Model.genMap (M := Y) (N := P) π.left hπ) π.left
      (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm sq₀
    rw [Model.genMap_q, hπ]
    exact IsPullback.of_hasPullback _ _
  exact ⟨{
    P := P, Y := Y, p₁ := (p1 Z).left, p₂ := (p2 Z).left, Δ := (dg Z).left, π := π.left
    h₁ := Over.w (p1 Z), h₂ := Over.w (p2 Z), hΔ := hΔ, hπ := hπ
    Δ₁ := pullback.diagonal_fst _, Δ₂ := pullback.diagonal_snd _
    prod := IsPullback.of_hasPullback _ _
    smP := hP, smY := hY, D := D, loc := B.loc
    blow := blowBC (OK l K) K (OK l K).subtype (XX Z).hom (dg Z).left π.left D (d + 1) P.q _ _ _ _ _ sq₀ sqΔ sqπ ⟨B⟩ }, het⟩

theorem UpperTheory.Gal.KunnethLefschetz.G.sqEx3 : CrystallineSemistableComparison.Onto.SqEx3 := fun l _ K _ M d _ h1 h2 => UpperTheory.Gal.KunnethLefschetz.G.sqCore l K M d h1 h2
