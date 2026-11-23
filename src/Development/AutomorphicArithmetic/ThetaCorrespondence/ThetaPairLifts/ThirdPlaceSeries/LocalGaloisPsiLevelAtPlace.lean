module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PsiReadWithLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglands

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.GalLoc.PsiLvl
theorem localGalois_psi_level_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := by
  intro _ _ hL
  refine _root_.GlobalTheory.GalLoc.PsiLvl.atMem_of_forall' fun K B f T w Z Wt p0 t nch n c => ?_
  obtain ⟨θ, hθ, hR⟩ := exists_theta_of_eq c.a.nt.eq c.a.nt.θ (_root_.GlobalTheory.GalLoc.PsiLvl.psiRead_withLoc_alt c.a.nt.toNBuilt)
  refine ⟨θ, hθ, fun g => ?_, fun u hu => ?_⟩
  · exact (c.row.grp.lvl0 g).trans (SetLike.ext_iff.mp c.a.all.exp.U_eq _)
  · have hu0 : (t.r.z.R.eG.trans t.r.z.cG) u ∈ (w.D Z).nexp.U := (c.row.grp.lvl0 u).1 u.2
    obtain ⟨i⟩ : Nonempty (w.D Z).ntw.Tw := by
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 (w.D Z).what₂.LL)
      exact ⟨nch.twI ((w.D Z).plEq.symm
        ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩)⟩
    obtain ⟨x, hx, hx'⟩ := c.row.grp.psi0 u hu0 i true
    have h2 := hR i _ hu0 hu
    have h3 : IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i) ((w.D Z).ntw.emb0 i x) =
        IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i) ((w.D Z).ntw.emb0 i
          ((psiUOf (w.D Z).nd (NX.xiRed (w.D Z)) θ ⟨(t.r.z.R.eG.trans t.r.z.cG) u, hu⟩ : (↥(w.D Z).LL0)ˣ) : ↥(w.D Z).LL0)) :=
      hx'.symm.trans h2
    have h4 := (IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i)).injective h3
    have h5 := ((w.D Z).ntw.emb0 i).injective h4
    exact (congrArg (fun z : ↥(w.D Z).LL0 => (z : (w.D Z).what₂.LL)) h5).symm.trans hx
end GlobalTheory.GalLoc.PsiLvl
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.exists_theta_heq_lvlPsi_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := by
  first | exact @_root_.GlobalTheory.GalLoc.PsiLvl.localGalois_psi_level_at_place_alt | exact _root_.GlobalTheory.GalLoc.PsiLvl.localGalois_psi_level_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.PsiLvl.localGalois_psi_level_at_place_alt <;> assumption)
end
end
