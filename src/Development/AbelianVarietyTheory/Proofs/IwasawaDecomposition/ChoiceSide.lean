module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : GlobalTheory.Published.LocalLanglandsGL}

section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.mtInput (x : MtInput D M tp.tup C.Q) : MtInput m.D (m.mt M) (m.tp tp).tup (m.ch C).Q := @_root_.GlobalTheory.HeightCounting.MtInput.mk (_) (_) (_) (_)
    (prod := (x.prod))
    (para := (x.para))
    (uni := (x.uni))
    (hyp := (x.hyp))
    (wt := (x.wt))
    (rat := (x.rat))
    (int := (x.int))
    (full := (x.full))

def Mv.ratIn {S} (x : RatIn D S) : RatIn m.D S := @_root_.GlobalTheory.HeightCounting.RatIn.mk (_) (_)
    (Sb := (x.Sb))
    (rho := (x.rho))
    (chi := (x.chi))
    (ks := (x.ks))
    (fd := (x.fd))
    (mk_fg := (x.mk_fg))
    (hL := (x.hL))
    (hs := (x.hs))
    (hL_zero := (x.hL_zero))
    (θ := (x.θ))
    (θ_ne := (x.θ_ne))
    (eig := (x.eig))
    (span := (x.span))
    (hL_int := (x.hL_int))
theorem Mv.rowDepth {rep} (x : RowDepth D rep) : RowDepth m.D rep := (x)
end

def Mv.host (x : HostTied D) : HostTied m.D := @_root_.Formalism.L2.Host.HostTied.mk (_)
    (fr := (x.fr))
    (jLL := (x.jLL))
    (embLL := (x.embLL))
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}

def Mv.chrN (x : NCharTied D cf C tp) : NCharTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NCharTied.mk (_) (_) (_) (_)
    (e1 := (x.e1))
    (unr_iff := (x.unr_iff))
    (frob := (x.frob))
    (tw := (x.tw))
    (infG := (x.infG))
    (csd := (x.csd))
    (muC := (x.muC))
    (etaT := (x.etaT))
    (etaTinv := (x.etaTinv))
    (plGw := (x.plGw))
theorem Mv.chrGal (x : NGalChrTied D cf C tp) : NGalChrTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NGalChrTied.mk (_) (_) (_) (_)
    (psi_is := (x.psi_is))
    (psiL := (x.psiL))
    (deltaRead := (x.deltaRead))
theorem Mv.oSplit (x : GlobalTheory.SplitCoef.OSplit D) : GlobalTheory.SplitCoef.OSplit m.D := (x)
theorem Mv.large (x : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large m.D := (x)
theorem Mv.bkLaw (x : BkLaw D) : BkLaw m.D := (x)

def Mv.omFrame (x : Formalism.L2.OmFrame D) : Formalism.L2.OmFrame m.D := @_root_.Formalism.L2.OmFrame.mk (_)
    (jE := (x.jE))
    (eOm := (x.eOm))
    (comm := (x.comm))
end

theorem Mv.pack_pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) {cf : CharFrame D₀} {C : NChoice D₀} (tp : TupTied D₀ cf C) :
    (⟨m.D, m.cf (cfL L cf), m.ch (chL L C), m.tp (tpL L tp)⟩ : Σ D : D7, Σ c : CharFrame D, Σ C : NChoice D, TupTied D c C) =
      ⟨withLoc (m.pre.loc L), cfL (m.pre.loc L) (m.pre.cf cf), chL (m.pre.loc L) (m.pre.ch C), tpL (m.pre.loc L) (m.pre.tp tp)⟩ :=
  (@Eq.refl (@Sigma D7 fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@Sigma.mk D7 (fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@D (@withLoc D₀ L) m) (@Sigma.mk (CharFrame (@D (@withLoc D₀ L) m)) (fun c ↦ @Sigma (NChoice (@D (@withLoc D₀ L) m)) fun C ↦ TupTied (@D (@withLoc D₀ L) m) c C) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) (@Sigma.mk (NChoice (@D (@withLoc D₀ L) m)) (fun C ↦ TupTied (@D (@withLoc D₀ L) m) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) C) (@ch (@withLoc D₀ L) m (@chL D₀ L C)) (@Mv.tp (@withLoc D₀ L) m (@cfL D₀ L cf) (@chL D₀ L C) (@tpL D₀ L cf C tp))))))

end GlobalTheory.LayerMove
end
