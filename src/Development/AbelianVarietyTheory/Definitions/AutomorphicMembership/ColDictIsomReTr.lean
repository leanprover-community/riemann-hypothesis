module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ColDictLReTr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def reG {X : HidaSetting D} (G : GoodOp X) : GoodOp (reX Z X) where
  Rg := (G.Rg)
  Rg_spec := (G.Rg_spec)



def eEECre {X : HidaSetting D} (G : GoodOp X) : EEC X G ≃ₗᵢ[ℂ] EEC (reX Z X) (reG Z G) := (LinearIsometryEquiv.refl ℂ ↥(EEC X G))



theorem measTie_reX {X : HidaSetting D} {hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I} (h : X.MeasTie hb) :
    (reX Z X).MeasTie hb := (h)



theorem measCompat_reX {X : HidaSetting D} {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ}
    (h : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ) : Formalism.L2.SG.MassDataConc.MeasCompatψ (reX Z X) ψ := (h)



theorem locCompat_reX {X : HidaSetting D} {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ} {w : D.what₂.Word}
    (h : Formalism.L2.SG.LocVol.LocCompatX X ψ w) : Formalism.L2.SG.LocVol.LocCompatX (reX Z X) ψ (wd Z w) := (h)

theorem colDict_congr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} (T : Transport X u F) (hK : X.LevelSubgroupCharacter)
    (L : Cu X u hK →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) (hL : ∀ x, L x = colDictL X T hK x) :
    (ColDictInto X T hK → ∀ x, L x ∈ (D.mem u).A.Mu0) ∧
    (ColDictBij X T hK → Function.Injective L ∧ ∀ φ ∈ (D.mem u).A.Mu0, ∃ x, L x = φ) ∧
    ∀ {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (hinj : Function.Injective (sharp hK cs)),
      ColDictIsom X T hK cs hinj → ∀ x y : ColT hinj, inner ℂ x y = (D.fm u).ipC 0 (L (toCu X hK x)) (L (toCu X hK y)) := by
  obtain rfl : L = colDictL X T hK := LinearMap.ext hL
  exact ⟨fun h => h, fun h => h, fun _ _ h => h⟩

section Col



variable {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (Y : Full X)



private theorem colDict_congr_reTr :
    (ColDictInto X T Y.hK → ColDictInto (reX Z X) (reTr Z T hy he) (reY Z Y).hK) ∧
    (ColDictBij X T Y.hK → ColDictBij (reX Z X) (reTr Z T hy he) (reY Z Y).hK) ∧
    ∀ (hF : FinX Y) (hF' : FinX (reY Z Y)),
      ColDictIsom X T Y.hK (Y.cs u) (hF.shInj u) →
      ColDictIsom (reX Z X) (reTr Z T hy he) (reY Z Y).hK ((reY Z Y).cs u) (hF'.shInj u) := by
  let L' := @colDictL (reD D Z) (reX Z X) u F' (@reTr D Z X u F F' T hy he) Y.hK
  -- Elaborate in the original indices of each term and let the kernel check the
  -- definitional equalities across reD, as in eCure.
  let L : Cu X u Y.hK →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := by
    run_tac
      let value ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `L')
      Lean.Elab.Tactic.liftMetaFinishingTactic (·.assign (.fvar value))
  have hL : ∀ x, L x = colDictL X T Y.hK x :=
    @colDictL_reTr D Z X u F F' T hy he Y.hK
  have h := colDict_congr T Y.hK L hL
  have result := And.intro h.1 (And.intro h.2.1
    (fun (hF : FinX Y) (_ : FinX (reY Z Y)) => h.2.2 (Y.cs u) (hF.shInj u)))
  run_tac
    let proof ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `result)
    Lean.Elab.Tactic.liftMetaFinishingTactic (·.assign (.fvar proof))

theorem colDictInto_reTr (h : ColDictInto X T Y.hK) : ColDictInto (reX Z X) (reTr Z T hy he) (reY Z Y).hK :=
  (colDict_congr_reTr Z T hy he Y).1 h



theorem colDictBij_reTr (h : ColDictBij X T Y.hK) : ColDictBij (reX Z X) (reTr Z T hy he) (reY Z Y).hK :=
  (colDict_congr_reTr Z T hy he Y).2.1 h



theorem colDictIsom_reTr (hF : FinX Y) (hF' : FinX (reY Z Y)) (h : ColDictIsom X T Y.hK (Y.cs u) (hF.shInj u)) :
    ColDictIsom (reX Z X) (reTr Z T hy he) (reY Z Y).hK ((reY Z Y).cs u) (hF'.shInj u) :=
  (colDict_congr_reTr Z T hy he Y).2.2 hF hF' h

end Col



theorem levelMatch_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hl : F'.cls0.lev = F.cls0.lev) (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (Y : Full X)
    (h : LevelMatch X T Y.hK) : LevelMatch (reX Z X) (reTr Z T hy he) (reY Z Y).hK := by
  unfold LevelMatch
  rw [hl]
  exact (h)

end GlobalTheory.Mem.SRe

end
