module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPairStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValuesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExtStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseFieldStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineDescent


private theorem descend_element_of_le_of_eq_K0 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) (m : ℕ)
    (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) :
    ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m),
      ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') :=
  GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT m y' hy'

set_option maxHeartbeats 60000000 in
private theorem descend_of_eq_K0_of_isCrys (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := by
  let W := (HW l).W K s LL h
  let W' := (HW l).W K' s LL h'
  let T' := @resLt l _ K K' LL hle T
  let toBase := @toTW l _ K K' LL hle T
  let f := @fMap l _ K K' W.GKs W'.GKs hm' htop
  -- Direct elimination avoids the cost of `cases` on the dependent goal.
  refine (descend_element_of_le_of_eq_K0 D HW F l K s LL h K' h' hle hK0 T hT m y' hy').elim fun y hy => ?_
  refine (GlobalTheory.T.X_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT z' hz').elim fun z hz => ?_
  refine ((GlobalTheory.WittTensorFixed.main l K' LL T').1
    (((F l).E K' s LL h').tie.jD T' y')).elim fun b' hb' => ?_
  refine (@cl_fit l _ D HW F K' s LL h' T' y' z' hyz' b' hb').elim fun c' hc' => ?_
  refine (@push_cocycle l _ (D.loc l) (D.locA l) K K' LL hle T W.GKs W'.GKs hm' htop c').elim
    fun c hc => ?_
  have hZf := hc.2
  let b := toBase b'
  have hb := (@toTW_φ l _ K K' LL hle T b').trans ((congrArg toBase hb').trans hy.2.symm)
  have hone (g : ↥W.GKs) : W'.resΓ (f g).1 = 1 ↔ W.resΓ g.1 = 1 :=
    (@resΓ_one_iff l _ (D.loc l) K' LL _ W' (f g).1).trans
      (@resΓ_one_iff l _ (D.loc l) K LL _ W g.1).symm
  have hzero (g : ↥W.GKs) (hg : W.resΓ g.1 = 1) :=
    (hZf b' g).trans ((congrArg toBase (hc'.2.1 (f g) ((hone g).2 hg))).trans
      (@toTW_zero l _ K K' LL hle T))
  refine (@lam_exists l _ D HW K' s LL h').elim fun lam' hlam' => ?_
  refine hlam'.2.2.2.1.elim fun g' hg' => ?_
  let lam := lam'.comp (@fHom l _ K K' W.GKs W'.GKs hm' htop)
  have hlamc : Continuous lam := hlam'.1.comp (@fMap_cont l _ K K' W.GKs W'.GKs hm' htop)
  have hlam1 (g : ↥W.GKs) (hg : lam g = 1) := (hone g).1 ((hlam'.2.1 (f g)).1 hg)
  let g₁ := @eMap l _ K K' hle W.GKs W'.GKs hm g'
  have hfe : f g₁ = g' := Subtype.ext (Subtype.ext rfl)
  have hg₁ : lam g₁ = Multiplicative.ofAdd 1 := (congrArg (fun g => lam' g) hfe).trans hg'
  have hZ₁ := (hZf b' g₁).trans
    ((congrArg (fun g => toBase (Zf (D.locA l) T' W'.GKs c' b' g)) hfe).trans
      ((congrArg toBase (hc'.2.2 g' ((hlam'.2.2.1 g').1 hg'))).trans hz.2.symm))
  have hall := GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline D HW F l K s LL h T hT c b lam hlamc hlam1 hzero g₁ hg₁ z hz.1 hZ₁
  refine (@lam_exists l _ D HW K s LL h).elim fun _ hlamK => ?_
  refine hlamK.2.2.2.1.elim fun g₀ hg₀ => ?_
  have hγ := (hlamK.2.2.1 g₀).1 hg₀
  refine (hall g₀).elim fun z₀ hz₀ => ?_
  have hyz := GlobalTheory.T.herr_cocycle_of_witt_tensor_relations D HW F l K s LL h T c b y z₀ g₀ hγ hb hz₀.2
  have hcl := GlobalTheory.T.herr_class_of_cocycle_values D HW F l K s LL h T c b y z₀ hyz g₀ hγ hb hzero hz₀.2
  exact ⟨y, z₀, hyz, hy.1, hz₀.1, c, c', hcl, hc'.1, hc.1⟩


set_option maxHeartbeats 4000000 in
theorem descend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := descend_of_eq_K0_of_isCrys D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT m y' z' hyz' hy' hz'

set_option maxHeartbeats 60000000 in
private theorem wach_pow_smul_of_good_ext : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l p K s LL h W E C T hT M hh hJ κ hκ
  refine (@base_setup l p D HW K s LL h).elim fun K' hK' =>
    hK'.elim fun h' hh' => hh'.elim fun hle hbase => ?_
  have htop := hbase.2.1
  have hiff := hbase.2.2
  let W' := (HW l).W K' s LL h'
  let T' := @resLt l p K K' LL hle T
  have hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ W.GKs :=
    fun g => (hiff _).2 g.2
  have hm' : ∀ g : ↥W.GKs, (g.1 : GQ l) ∈ GK K' := fun g => (hiff g.1).1 g.2
  have hT' := @restrict_crys l p D K K' LL hle T hT
  have hJ' := @restrict_jumps l p D HW K s LL h K' h' hle T hT M hh hJ
    (@GlobalTheory.T.hodgeTateJump_restrict_finite_ext l p (D.loc l) (D.locA l) (D.locT l)
      K K' LL hle T.V T.acg T.modLL T.modQp T.towQp T.fdim T.ρ hT)
  refine (@pull_h1f l p (D.loc l) K K' LL hle T W.GKs W'.GKs hm κ hκ).elim fun cκ hcκ =>
    hcκ.elim fun cκ' hκ' => ?_
  refine (@GlobalTheory.T.H1f_class_of_wach_pair D HW F Cm l p K' s LL h' T' hT' htop
    (fun _ => mx M) (fun _ => mx hh) hJ' (Submodule.Quotient.mk cκ') hκ'.2.1).elim
    fun n hn => hn.elim fun y' hy' => hy'.elim fun z' hz' => hz'.elim fun hyz' hpair' => ?_
  have : Nonempty (Let K') := ⟨0⟩
  have hmx : mx (fun _ : Let K' => mx M) = mx M := ciSup_const
  have hy'mx := (congrArg (fun k : ℕ => y' ∈ invN W' T' (W'.Q ^ k)) hmx).mp hpair'.1
  refine (@descend D HW F l p K s LL h K' h' hle hbase.1 htop hm hm' T hT (mx M) y' z' hyz' hy'mx hpair'.2.1).elim
    fun y hy => hy.elim fun z hz => hz.elim fun hyz hpair => ?_
  refine hpair.2.2.elim fun c hc => hc.elim fun c' hcc' => ?_
  have hpush := @push_class l p K K' LL hle T W.GKs W'.GKs hm hm' htop c cκ c' cκ' hcc'.2.2 hκ'.2.2
    (l ^ n) (hcc'.2.1.trans hpair'.2.2)
  exact ⟨n, y, z, hyz, hpair.1, hpair.2.1,
    hcc'.1.symm.trans (hpush.trans (congrArg (fun x => (l ^ n : ℕ) • x) hκ'.1))⟩


set_option maxHeartbeats 4000000 in
theorem pow_smul_from_complex : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := wach_pow_smul_of_good_ext

end GlobalTheory.NL.CrystallineDescent
