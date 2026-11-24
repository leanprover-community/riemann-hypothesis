module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.LimSurjFil
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime]

def βS (hC : B.Compat l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) :
    Sys.Hom (B.HcSys F κ k j) (MSys (F.pt κ) j) (RingHom.id _) where
  f n := B.β F κ k n j
  comm n x := Eq.symm (hC.red F κ k (m := n + 1) n.le_succ j x)

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem atlas_of {M : Model l K} (h : M.Sm) : ∃ d, Nonempty ((B.schFn M.p).Atlas d) := by
  have : Smooth M.p := h.2
  have : IsProper M.p := AdicGeo.proper_p (M := M) h.1
  exact _root_.GlobalTheory.CompanionTheory.SchAtlas.exists_atlas (O := OK l K) (X := M.X) M.p

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

def bβ (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (show Sys.Hom (M.HS false j) (M.MS j) (RingHom.id _) from
    βS hC (B.schFn M.p) (okToOC l K) false j).lim

def bβ' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H' a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (show Sys.Hom (M.HS true j) (M.MS j) (RingHom.id _) from
    βS hC (B.schFn M.p) (okToOC l K) true j).lim

private theorem limit_bounds (hMain : B.Main l) (hC : B.Compat l)
    {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)
    (hAtlas : ∃ d, Nonempty (F.Atlas d)) (j : ℕ) (t : Acris l)
    (hPeriod : ∃ ε : B.Eps l, ∃ u : Acris l, IsUnit u ∧ t = ε.μ * u) :
    ∃ n : ℕ, (∀ k, UpTo (t ^ n) (βS hC F κ k j).lim) ∧
      ∀ y : (MSys (F.pt κ) j).lim, ∃ x : (B.HcSys F κ false j).lim,
        (∀ i, x.1 i ∈ B.HcFil F κ false i n j) ∧ (βS hC F κ false j).lim x = t ^ n • y := by
  refine hAtlas.elim fun d hA => hA.elim fun A =>
    hPeriod.elim fun ε hε => hε.elim fun u hu => (hMain d j).elim fun N hN => ?_
  have hLevel := hN F κ ε A
  refine ⟨2 * N, ?_, ?_⟩
  · intro k
    let φ := βS hC F κ k j
    have hUpTo (n : ℕ) := (hLevel n).1 k
    exact ⟨GlueBL.lim_inj φ ε.μ u t N hu.2 hUpTo, GlueBL.lim_surj φ ε.μ u t N hu.2 hUpTo⟩
  · exact GlueBL.lim_surj_fil (βS hC F κ false j) ε.μ u t N hu.2
      (fun n r => B.HcFil F κ false n r j)
      (fun n r => hC.smul_fil F κ false n r j ε.μ (ε.μ_mem false (PAlg.base l) n))
      (fun n => ((hLevel n).1 false).1) (fun n => (hLevel n).2)

-- The same exponent works for both comparison maps and the filtered lift.
private theorem model_bounds (hMain : B.Main l) (hC : B.Compat l) {M : Model l K}
    (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, UpTo ((per l K).t ^ n) (bβ Amp hC a j) ∧
      UpTo ((per l K).t ^ n) (bβ' Amp hC a j) ∧
      ∀ y, ∃ x, (dat Amp).fil a j n x ∧ bβ Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨n, hb, hf⟩ := limit_bounds hMain hC (B.schFn M.p) (okToOC l K) (atlas_of hM) j
    (per l K).t (GlueBE.exists_eps_period_t_unit l K)
  exact ⟨n, hb false, hb true, hf⟩

theorem f_inj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ Amp hC a j x = 0 → (per l K).t ^ n • x = 0 :=
  (model_bounds Amp hMain hC a hM j).imp fun _ h => h.1.1

theorem f_inj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ' Amp hC a j x = 0 → (per l K).t ^ n • x = 0 :=
  (model_bounds Amp hMain hC a hM j).imp fun _ h => h.2.1.1

theorem f_surj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, bβ' Amp hC a j x = (per l K).t ^ n • y :=
  (model_bounds Amp hMain hC a hM j).imp fun _ h => h.2.1.2

theorem f_surj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, (dat Amp).fil a j n x ∧ bβ Amp hC a j x = (per l K).t ^ n • y :=
  (model_bounds Amp hMain hC a hM j).imp fun _ h => h.2.2

end GlueB'

end CrystallineSemistableComparison
