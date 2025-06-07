/-
Copyright (c) 2024 XYZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYZ
-/

import Mathlib

set_option autoImplicit false


-----------------------------------------------------------------------------------------------------------------------------------------------
-- Misc Preliminary Results to PR to Mathlib
-----------------------------------------------------------------------------------------------------------------------------------------------

theorem separableInductiveLimit_of_separable {X : ℕ → Type*} [(n : ℕ) → MetricSpace (X n)]
    [hs : (n : ℕ) → TopologicalSpace.SeparableSpace (X n)] {f : (n : ℕ) → X n → X (n + 1)}
    (I : ∀ (n : ℕ), Isometry (f n)) :
    TopologicalSpace.SeparableSpace (Metric.InductiveLimit I) := by
  constructor
  choose hsX hcX hdX using (fun n ↦ TopologicalSpace.exists_countable_dense (X n))
  let s := ⋃ (i : ℕ), (Metric.toInductiveLimit I i '' (hsX i))
  refine ⟨s, Set.countable_iUnion (fun n => (hcX n).image _), ?_⟩
  rintro ⟨n, x⟩
  refine Metric.mem_closure_iff.mpr (fun ε hε ↦ ?_)
  obtain ⟨b, hb⟩ := Metric.mem_closure_iff.mp (hdX n x) ε hε
  refine ⟨Metric.toInductiveLimit I n b, ?_, ?_⟩
  · simp only [s, Set.mem_iUnion, Set.mem_image]
    refine ⟨n, b, hb.1, rfl⟩
  · convert hb.2
    change Metric.inductiveLimitDist f ⟨n, x⟩ ⟨n, b⟩ = dist x b
    rw [Metric.inductiveLimitDist_eq_dist I ⟨n, x⟩ ⟨n, b⟩ n (le_refl n) (le_refl n), Nat.leRecOn_self,
        Nat.leRecOn_self]

theorem TopologicalSpace.Embedding.separableSpace {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [SecondCountableTopology β] {f : α → β} (hf : Topology.Embedding f) :
    TopologicalSpace.SeparableSpace α := by
  have := hf.secondCountableTopology
  exact SecondCountableTopology.to_separableSpace

open Pointwise

lemma inf_sub_sup_le_inf {α : Type*} {f g : α → ℝ}
 (fpos : BddBelow (Set.range f)) (gpos : BddBelow (Set.range g))  (hb : BddAbove (Set.range |f - g|)):
    iInf g - iSup |f - g| ≤ iInf f := by
  by_cases hα : Nonempty α
  · rw [iInf, iSup, ← csInf_sub ⟨g (Classical.choice hα), by simp⟩ _ _ (by exact hb)]
    · apply le_csInf ⟨f (Classical.choice hα), by simp⟩
      rintro _ ⟨x, rfl⟩
      refine @csInf_le_of_le _ _ ({g x | x} - {|f x - g x| | x})
        (f x) (g x - |f x - g x|) ?_ ⟨g x, (by simp), |f x - g x|, by simp, by ring⟩ ?_
      · simp_rw [sub_eq_add_neg]
        apply BddBelow.add (by aesop) (BddAbove.neg hb)
      · rw [abs_sub_comm]
        suffices h : g x - f x ≤ |g x - f x| by linarith
        exact le_abs_self (g x - f x)
    · exact gpos
    · set z₀ := Classical.choice hα
      refine ⟨|f z₀ - g z₀|, by simp⟩
  · simp [not_nonempty_iff.mp hα]

lemma abs_sub_inf_le_sup {α : Type*} {f g : α → ℝ}
 (fpos : BddBelow (Set.range f)) (gpos : BddBelow (Set.range g)) (hb : BddAbove (Set.range |f - g|)):
    |iInf f - iInf g| ≤ iSup |f - g| := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [inf_sub_sup_le_inf fpos gpos hb]
    · rw [abs_sub_comm] at *
      linarith [inf_sub_sup_le_inf gpos fpos hb]

lemma eq_zero_of_sSup_eq_zero (s : Set ℝ) (hb : BddAbove s) (snonneg : ∀ x ∈ s, 0 ≤ x)
    (hsup : sSup s = 0) : ∀ x ∈ s, x = 0 := by
  refine (fun x xs ↦ le_antisymm (by rw [← hsup]; exact le_csSup hb xs) (snonneg x xs))


-----------------------------------------------------------------------------------------------------------------------------------------------
-- Definition & Setup for Katetov Maps
-----------------------------------------------------------------------------------------------------------------------------------------------

variable {α : Type*} [MetricSpace α]

/-- A real valued function `f` on a metric space is Katetov if
  it is 1-Lipschitz and for all `x` and `y` we have `dist x y ≤ f x + f y`. -/
@[mk_iff]
structure IsKatetov (f : α → ℝ) : Prop where
  /-- `f` is 1-Lipschitz -/
  abs_sub_le_dist : ∀ x y, |f x - f y| ≤ dist x y
  /-- `f` obeys the Katetov "triangle inequality"  -/
  dist_le_add : ∀ x y, dist x y ≤ f x + f y

/-- The type of Katetov maps from `α`
-/
structure KatetovMap (α : Type*) [MetricSpace α] where
  /-- The function `α → ℝ` -/
  protected toFun : α → ℝ
  /-- Proposition that `toFun` is a Katetov map -/
  protected isKatetovtoFun : IsKatetov toFun

/-- The type of Katetov maps from `α`. -/
notation "E(" α ")" => KatetovMap α

section

/-- `KatetovMapClass F α` states that `F` is a type of Katetov maps. -/
class KatetovMapClass (F : Type*) (α : Type*) [MetricSpace α] [FunLike F α  ℝ] : Prop where
  map_katetov (f : F) : IsKatetov f

end

export KatetovMapClass (map_katetov)

section KatetovMapClass

variable {F α : Type*} [MetricSpace α] [FunLike F α  ℝ]
variable [KatetovMapClass F α]

/-- Coerce a bundled morphism with a `KatetovMapClass` instance to a `KatetovMap`. -/
@[coe] def toKatetovMap (f : F) : E(α) := ⟨f, map_katetov f⟩

instance : CoeTC F E(α) := ⟨toKatetovMap⟩

end KatetovMapClass

namespace KatetovMap

variable {α : Type*} [MetricSpace α]

instance funLike : FunLike E(α) α ℝ where
  coe := KatetovMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance toKatetovMapClass : KatetovMapClass E(α) α where
  map_katetov := KatetovMap.isKatetovtoFun

@[simp]
theorem toFun_eq_coe {f : E(α)} : f.toFun = (f : α → ℝ) := rfl

instance : CanLift (α → ℝ) E(α) DFunLike.coe IsKatetov := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩
/-- See Topology/ContinuousFunction.Basic -/
def Simps.apply (f : E(α)) : α → ℝ := f

initialize_simps_projections KatetovMap (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F α ℝ] [KatetovMapClass F α] (f : F) :
    ⇑(f : E(α)) = f := rfl

@[ext]
theorem ext {f g : E(α)} (h : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ h

/-- Copy of a `KatetovMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. See Topology/ContinuousFunction.Basic -/
protected def copy (f : E(α)) (φ' : α → ℝ) (h : φ' = f) : E(α) where
  toFun := φ'
  isKatetovtoFun := h.symm ▸ f.isKatetovtoFun

@[simp]
theorem coe_copy (f : E(α)) (φ' : α → ℝ) (h : φ' = f) : ⇑(f.copy φ' h) = φ' :=
  rfl

theorem copy_eq (f : E(α)) (φ' : α → ℝ) (h : φ' = f) : f.copy φ' h = f :=
  DFunLike.ext' h

variable {f g : E(α)}

theorem katetov_set_coe (s : Set E(α)) (f : s) : IsKatetov (f : α → ℝ) :=
  f.1.isKatetovtoFun

theorem coe_injective : @Function.Injective E(α) (α → ℝ) (↑) :=
  fun f g h ↦ by cases f; cases g; congr

@[simp]
theorem coe_mk (f : α → ℝ) (h : IsKatetov f) : ⇑(⟨f, h⟩ : E(α)) = f :=
  rfl


-----------------------------------------------------------------------------------------------------------------------------------------------
-- Properties of Katetov Maps
-----------------------------------------------------------------------------------------------------------------------------------------------

lemma abs_sub_dist_le {f : E(α)} {x y: α} : |f x - dist x y| ≤ f y := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact neg_le_sub_iff_le_add.mpr <| (map_katetov f).dist_le_add x y
  · exact sub_le_comm.mpr <| le_of_abs_le <| (map_katetov f).abs_sub_le_dist x y

theorem bddAbove_range_abs_sub {f g : E(α)} : BddAbove (Set.range (|f - g| : α → ℝ)) := by
  by_cases hn : Nonempty α
  · let x₀ := Classical.choice ‹Nonempty α›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩; rw [← hx]
    calc
    _ ≤ |f x - dist x x₀| + |g x - dist x x₀| := by rw [← abs_sub_comm _ (g x)]; simp [abs_sub_le]
    _ ≤ f x₀ + g x₀ := add_le_add abs_sub_dist_le abs_sub_dist_le
  · refine ⟨0, fun _ ⟨x, _⟩ ↦ False.elim (hn ⟨x⟩)⟩

theorem katetov_nonneg {f : E(α)} {x : α} : 0 ≤ f x := by
  have : 0 ≤ f x + f x := by rw [← dist_self x]; exact (map_katetov f).dist_le_add x x
  apply nonneg_add_self_iff.mp this

noncomputable instance instKatetovMetricSpace : MetricSpace E(α) where
  dist f g := iSup (|f - g| : α → ℝ)
  dist_self f := by
    simp only [dist, sub_self, abs_zero]
    exact Real.iSup_const_zero
  dist_comm f g := by simp [dist, abs_sub_comm]
  dist_triangle f g h := by
    by_cases hα : Nonempty α
    · refine Real.iSup_le (fun i ↦ ?_) ?_
      · refine le_trans (abs_sub_le (f i) (g i) (h i)) (add_le_add ?_ ?_) <;>
        { rw [← Pi.sub_apply, ← Pi.abs_apply]; apply le_ciSup bddAbove_range_abs_sub }
      · apply add_nonneg <;> {apply Real.iSup_nonneg; intro i; apply abs_nonneg}
    · simp only [not_nonempty_iff.mp hα , Real.iSup_of_isEmpty, add_zero, le_refl]
  eq_of_dist_eq_zero := by
    intro f g h
    apply eq_zero_of_sSup_eq_zero at h
    · ext x; exact eq_of_sub_eq_zero <| abs_eq_zero.mp (h |f x - g x| ⟨x, rfl⟩)
    · apply bddAbove_range_abs_sub
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _

theorem dist_coe_le_dist (f g : E(α)) (x : α) : dist (f x) (g x) ≤ dist f g :=
  by refine le_csSup bddAbove_range_abs_sub (by simp [dist])

theorem dist_le {C :ℝ} (C0 : (0 : ℝ) ≤ C) (f g : E(α)):
    dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  refine ⟨fun h x => le_trans (dist_coe_le_dist _ _ x) h, fun H ↦ ?_⟩
  simp [dist]; apply Real.sSup_le (by simp [*] at *; assumption) (C0)

noncomputable instance : CompleteSpace E(α) :=
  Metric.complete_of_cauchySeq_tendsto fun (u : ℕ → E(α)) (hf : CauchySeq u) => by
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have u_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist _ _ x) (b_bound n m N hn hm)
    have ux_cau : ∀ x : α, CauchySeq fun n => u n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, u_bdd x, b_lim⟩
    choose f hf using fun x => cauchySeq_tendsto_of_complete (ux_cau x)
    have fF_bdd : ∀ x N, dist (u N x) (f x) ≤ b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hf x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => u_bdd x N n N (le_refl N) hn⟩)
    have kat_f : IsKatetov f := by
      have h : ∀ x y, ∀ ε > 0, |f x - f y| ≤ 2*ε + dist x y ∧ dist x y ≤ f x + f y + 2*ε := by
        intro x y ε εpos
        rcases Metric.tendsto_atTop.mp (hf x) ε εpos with ⟨Nx, hNx⟩
        rcases Metric.tendsto_atTop.mp (hf y) ε εpos with ⟨Ny, hNy⟩
        simp [dist] at *
        set N := max Nx Ny
        specialize hNx N (le_max_left _ _)
        specialize hNy N (le_max_right _ _)
        constructor
        · calc
          _ = |(f x - (u N) x) + ((u N) y - f y) + ((u N x) - (u N y))|     := by ring_nf
          _ ≤ |(f x - (u N) x)| + |((u N) y - f y)| + |((u N x) - (u N y))| := by
              repeat apply (abs_add ..).trans; gcongr; try exact abs_add _ _
          _ ≤ 2*ε + dist x y := by
              rw [abs_sub_comm (f x)]
              linarith [(map_katetov (u N)).abs_sub_le_dist x y]
        · calc
          _ ≤ u N x + u N y := (map_katetov (u N)).dist_le_add x y
          _ = f x + f y + (u N x - f x) + (u N y - f y) := by ring_nf
          _ ≤ f x + f y + 2*ε := by
            linarith [le_of_lt (lt_of_abs_lt hNx), le_of_lt (lt_of_abs_lt hNy)]
      constructor <;>
        { refine fun x y ↦ le_of_forall_pos_le_add (fun ε εpos ↦ ?_)
          linarith [h x y (ε/2) (half_pos εpos)]}
    · use ⟨f, kat_f⟩
      refine' tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) _ b_lim)
      refine (fun N ↦ (dist_le (b0 N) (u N) ⟨f, kat_f⟩).mpr (fun x => fF_bdd x N))

open Set TopologicalSpace

/-- The Katetov map from an empty type -/
def empty_katetovmap (α : Type*) [MetricSpace α] [IsEmpty α] : E(α) := by
  refine ⟨fun x ↦ (IsEmpty.false x).elim, ?_⟩
  constructor <;> {intro x; exact (IsEmpty.false x).elim}

theorem emptymap_unique [IsEmpty α] (f g : E(α)) : f = g := by
  ext x; exact (IsEmpty.false x).elim

theorem isometry_coe (α : Type*) [MetricSpace α] [Fintype α] : Isometry (fun f : E(α) ↦ ⇑f) := by
  refine Isometry.of_dist_eq (fun f g ↦ ?_)
  simp only [dist]
  by_cases hα : Nonempty α
  · rw [← Finset.sup'_eq_sup, Finset.sup'_eq_csSup_image]
    simp [nndist, dist, NNReal.coe_sSup]; congr; ext x; simp
    refine ⟨Classical.choice ‹Nonempty α›, by simp only [Finset.mem_univ]⟩
  · have : IsEmpty α := not_nonempty_iff.mp hα
    simp [emptymap_unique f g]

instance instSecondCountableKatetovMaps {α : Type*} [MetricSpace α] (hα : Fintype α) :
    SecondCountableTopology E(α) := by
  exact (isometry_coe α).isEmbedding.secondCountableTopology

instance instSeparableSpaceKatetovMaps {α : Type*} [MetricSpace α] (hα : Fintype α) :
  SeparableSpace E(α) := by
  exact @TopologicalSpace.SecondCountableTopology.to_separableSpace _ _
    (instSecondCountableKatetovMaps hα)


-----------------------------------------------------------------------------------------------------------------------------------------------
-- Frechet-Kuratowski Embedding for Katetov Maps
-----------------------------------------------------------------------------------------------------------------------------------------------

namespace DistPointEmbedding

theorem isKatetov_dist_point {α : Type*} [MetricSpace α] (x : α) : IsKatetov (fun y ↦ dist x y) := by
  constructor <;> (intro y z; rw [dist_comm x y])
  · rw [dist_comm x z]; exact abs_dist_sub_le y z x
  · exact dist_triangle y x z

theorem isometry_dist_point_embedding {α : Type*} (h : Nonempty α ) [MetricSpace α] :
  Isometry (fun x ↦ (⟨fun y ↦ dist x y, isKatetov_dist_point x⟩ : E(α)))
  := by
  · refine Isometry.of_dist_eq (fun x y ↦ le_antisymm ?_ ?_)
    · exact Real.iSup_le (fun z ↦ abs_dist_sub_le x y z) dist_nonneg
    · refine (Real.le_sSup_iff bddAbove_range_abs_sub ?_).mpr  ?_
      · have x₀ := Classical.choice ‹Nonempty α›; use |dist x x₀ - dist y x₀|; simp
      · simp; refine fun ε εpos ↦ ⟨x, ?_⟩
        rw [dist_self, zero_sub, abs_neg, dist_comm, abs_of_nonneg (dist_nonneg)]
        exact add_lt_of_neg_right (dist y x) εpos

theorem exists_isometric_embedding (α : Type*) [MetricSpace α] : ∃ f : α → E(α), Isometry f := by
    by_cases hα : Nonempty α
    · exact ⟨(fun x ↦ (⟨fun y ↦ dist x y, isKatetov_dist_point x⟩ : E(α))),
        isometry_dist_point_embedding hα⟩
    · refine ⟨fun _ ↦ @empty_katetovmap _ _ (not_nonempty_iff.mp hα), fun x ↦ ?_⟩
      exact ((not_nonempty_iff.mp hα ).false x).elim

noncomputable def dist_point_embedding (α : Type*) [MetricSpace α] : α ↪ E(α) := by
  choose f h using exists_isometric_embedding α; refine ⟨f, h.injective⟩

protected theorem dist_point_embedding.isometry (α : Type*) [MetricSpace α] :
    Isometry (dist_point_embedding α) :=
  Classical.choose_spec <| exists_isometric_embedding α

end DistPointEmbedding

namespace KatetovExtension

open DistPointEmbedding Pointwise


-----------------------------------------------------------------------------------------------------------------------------------------------
-- Extension of Katetov Maps
-----------------------------------------------------------------------------------------------------------------------------------------------

noncomputable def extend {α β : Type*} [MetricSpace α] [MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) (f : E(β)) : E(α) := by
  by_cases hβ : Nonempty β
  · refine ⟨fun x ↦ iInf ((f : β → ℝ) + dist x ∘ ρ) , ?_⟩
    constructor <;> intro x y
    · calc
      _ ≤ iSup |(f : β → ℝ) + dist x ∘ ρ - ((f : β → ℝ) + dist y ∘ ρ)| := by
        refine abs_sub_inf_le_sup ?_ ?_ ?_
        · refine ⟨0, mem_lowerBounds.mpr ?_⟩
          rw [Set.forall_mem_range]
          refine fun x ↦ add_nonneg katetov_nonneg dist_nonneg
        · refine ⟨0, mem_lowerBounds.mpr ?_⟩
          rw [Set.forall_mem_range]
          refine fun x ↦ add_nonneg katetov_nonneg dist_nonneg
        · use dist x y; rintro _ ⟨z, rfl⟩; simp [abs_dist_sub_le]
      _ = iSup |dist x ∘ ρ - dist y ∘ ρ| := by ring_nf
      _ ≤ _ := Real.iSup_le (fun z ↦ abs_dist_sub_le x y (ρ z)) dist_nonneg
    · refine le_add_ciInf (fun z ↦ le_ciInf_add (fun z₁ ↦ ?_))
      calc
      _ ≤ dist x (ρ z₁) + dist y (ρ z) + dist z z₁ := by
          rw [← hρ.dist_eq, dist_comm (ρ z), dist_comm _ (ρ z)]
          linarith [ dist_triangle4 x (ρ z₁) (ρ z) y]
      _ ≤ _ := by simp; linarith [(map_katetov f).dist_le_add z z₁]
  · by_cases hα : Nonempty α
    · exact ⟨_, isKatetov_dist_point (Classical.choice hα)⟩
    · exact @empty_katetovmap _ _ (not_nonempty_iff.mp hα)

def restrict {α β: Type*} [MetricSpace α][MetricSpace β] (ρ : β → α) (hρ : Isometry ρ)
    (f : E(α)) : E(β) := by
  refine ⟨fun x ↦ f (ρ x), ?_⟩
  constructor <;> intro x y
  · rw [← hρ.dist_eq]; exact (map_katetov f).abs_sub_le_dist (ρ x) (ρ y)
  · rw [← hρ.dist_eq]; exact (map_katetov f).dist_le_add (ρ x) (ρ y)

theorem inf_add_dist_point {α β: Type*} [MetricSpace α][MetricSpace β] (ρ : β → α)
    (hρ : Isometry ρ) (f : E(β)) (x : β) : iInf (⇑f + dist (ρ x) ∘ ρ) = f x := by
  refine le_antisymm ?_ ?_
  · rw [← add_zero (f x), ← dist_self (ρ x),
        ← @Function.comp_apply _ _ _ (dist (ρ x)) _ _, ← Pi.add_apply]
    refine ciInf_le ⟨0, Set.mem_setOf.mpr ?_⟩ x
    rintro _ ⟨z, hz, rfl⟩
    exact add_nonneg katetov_nonneg dist_nonneg
  · have : Nonempty β := ⟨x⟩
    refine le_ciInf (fun z ↦ ?_)
    simp [hρ.dist_eq]
    linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x z]

theorem restrict_extend_eq_id {α β: Type} [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) (f : E(β)) :
    restrict ρ hρ (extend ρ hρ f) = f := by
  ext x; simp [extend, restrict]
  by_cases hβ : Nonempty β
  · simp [hβ]; exact inf_add_dist_point ρ hρ f x
  · exact False.elim (hβ ⟨x⟩)

theorem isometry_extend {α β : Type*} [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) : Isometry (fun f ↦ extend ρ hρ f) := by
  by_cases hβ : Nonempty β
  · refine Isometry.of_dist_eq (fun f g ↦ le_antisymm ?_ ?_)
    · refine Real.iSup_le (fun x ↦ ?_) dist_nonneg
      simp [dist, extend, hβ]
      have hpos : ∀ f : E(β), BddBelow (Set.range ((f : β → ℝ) + dist x ∘ ρ)) := by
        refine fun f ↦ ⟨0, mem_lowerBounds.mpr ?_⟩
        rw [Set.forall_mem_range]
        refine fun x ↦ add_nonneg katetov_nonneg dist_nonneg
      have hb : BddAbove (range |((f : β → ℝ) + dist x ∘ ρ) - ((g : β → ℝ) + dist x ∘ ρ)|) := by
        simp; exact bddAbove_range_abs_sub
      rw [show iSup (|f - g| : β → ℝ)
          = iSup |(f : β → ℝ) + dist x ∘ ρ - ((g : β → ℝ) + dist x ∘ ρ)| by congr 1; simp]
      exact (abs_sub_inf_le_sup (hpos f) (hpos g) hb)
    · refine Real.iSup_le (fun x ↦ ?_) dist_nonneg
      simp [extend, hβ]
      refine le_csSup_of_le bddAbove_range_abs_sub ⟨(ρ x), ?_⟩ (le_refl |f x - g x|)
      simp [inf_add_dist_point ρ hρ f x, inf_add_dist_point ρ hρ g x]
  · refine Isometry.of_dist_eq (fun f g ↦ ?_)
    simp [@emptymap_unique _ _ (not_nonempty_iff.mp hβ) f g]

theorem exists_isometric_embedding(α β : Type) [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) :
  ∃ f : E(β) → E(α), Isometry f := ⟨fun f ↦ extend ρ hρ f, isometry_extend ρ hρ⟩


-----------------------------------------------------------------------------------------------------------------------------------------------
-- Finitely-supported Katetov Maps
-----------------------------------------------------------------------------------------------------------------------------------------------

def FinSuppKatetovMaps : Set E(α) :=
    ⋃ s : Finset α, Set.range (extend (fun x : s ↦ (x : α)) isometry_id)

/-- The type of Katetov maps from `α`. -/
scoped notation "E(" α "," " ω)" => @FinSuppKatetovMaps α _

noncomputable instance : MetricSpace E(α, ω) := by infer_instance

def emptyFinSuppKatetovmap (α : Type*) [MetricSpace α] [IsEmpty α] : E(α, ω) := by
  refine ⟨empty_katetovmap α, ?_⟩
  refine Set.mem_iUnion.mpr ⟨∅, ⟨@empty_katetovmap {x | x ∈ (∅ : Finset α)} _ (by simp), ?_⟩⟩
  simp only [extend, Finset.not_mem_empty, not_nonempty_iff.mpr, ↓reduceDIte]

theorem empty_finsupp_eq_empty {α : Type*} [MetricSpace α] [IsEmpty α] :
    emptyFinSuppKatetovmap α = empty_katetovmap α := by rfl

theorem emptyfinsuppmap_unique [IsEmpty α] (f g : E(α, ω)) : f = g := by
  ext x; exact (IsEmpty.false x).elim

theorem isFinSuppKatetov_dist_point {α : Type*} [MetricSpace α] (x : α) :
    ⟨(fun y ↦ dist x y), isKatetov_dist_point x⟩ ∈ E(α, ω) := by
  apply Set.mem_iUnion.mpr
  refine ⟨{x}, Set.mem_range.mpr ?_⟩
  refine ⟨⟨fun y ↦ dist x y, ?_⟩, ?_⟩
  · constructor <;> (intro y z; rw [dist_comm x y])
    · rw [dist_comm x z]; exact abs_dist_sub_le (y : α) (z : α) x
    · exact dist_triangle (y : α) x z
  · ext z; simp [extend, dist_comm]

theorem isometry_dist_point_embedding {α : Type*} (h : Nonempty α ) [MetricSpace α] :
    Isometry (fun x : α ↦ (⟨⟨fun y ↦ dist x y, isKatetov_dist_point x⟩,
      isFinSuppKatetov_dist_point x⟩ : E(α, ω)))
  := by
  · refine Isometry.of_dist_eq (fun x y ↦ le_antisymm ?_ ?_)
    · refine Real.iSup_le ?_ dist_nonneg
      · simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
        refine fun z ↦ abs_dist_sub_le x y z
    · refine (Real.le_sSup_iff bddAbove_range_abs_sub ?_).mpr  ?_
      · have x₀ := Classical.choice ‹Nonempty α›
        use |dist x x₀ - dist y x₀|; simp
      · simp; refine fun ε εpos ↦ ⟨x, ?_⟩
        rw [dist_self, zero_sub, abs_neg, dist_comm, abs_of_nonneg dist_nonneg]
        exact add_lt_of_neg_right (dist y x) εpos

theorem finSuppKatetov_exists_isometric_embedding (α : Type*) [MetricSpace α] :
    ∃ f : α → E(α, ω), Isometry f := by
  by_cases h : Nonempty α
  · refine ⟨fun x : α ↦ ⟨⟨fun y ↦ dist x y, isKatetov_dist_point x⟩,
      isFinSuppKatetov_dist_point x⟩, isometry_dist_point_embedding h⟩
  · refine ⟨fun _ ↦ ⟨@empty_katetovmap _ _ (not_nonempty_iff.mp h), ?_⟩, fun y ↦ ?_⟩
    · exact ((not_nonempty_iff.mp h).false ‹α›).elim
    · exact ((not_nonempty_iff.mp h).false y).elim

noncomputable def distPointEmbeddingFinsuppKatetov (α : Type*) [MetricSpace α] : α ↪ E(α, ω) := by
  choose f h using finSuppKatetov_exists_isometric_embedding α; refine ⟨f, h.injective⟩

protected theorem distPointEmbeddingFinsuppKatetov.isometry (α : Type*) [MetricSpace α] :
    Isometry (distPointEmbeddingFinsuppKatetov α) :=
    Classical.choose_spec <| finSuppKatetov_exists_isometric_embedding α


lemma min_point {β : Type*} [MetricSpace β] (f: E(β)) (x : β): sInf {(f : E(β)) z + dist x z | (z : β)} = f x:= by
        refine le_antisymm ?_ ?_
        · refine csInf_le ?_ ⟨x, by simp only [dist_self, add_zero]⟩
          refine ⟨0, Set.mem_setOf.mpr ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact add_nonneg (katetov_nonneg) (dist_nonneg)
        · apply le_csInf
          · refine ⟨f x + dist x x, ⟨x, by simp only [dist_self, add_zero]⟩⟩
          · rintro _ ⟨z, hz, rfl⟩
            linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x z]

lemma min_point₁ {β : Type*} [MetricSpace β] (f: E(β)) (x : β) : iInf ((f : β → ℝ) + dist x) = f x:= by
        refine le_antisymm ?_ ?_
        · refine csInf_le ?_ ⟨x, by simp only [Pi.add_apply, dist_self, add_zero]⟩
          refine ⟨0, Set.mem_setOf.mpr ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact add_nonneg (katetov_nonneg) (dist_nonneg)
        · apply le_csInf
          · refine ⟨f x + dist x x, ⟨x, by simp only [Pi.add_apply, dist_self, add_zero]⟩⟩
          · rintro _ ⟨z, hz, rfl⟩
            simp only [Pi.add_apply]
            linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x z]


lemma min_point₂ {α β : Type*} [MetricSpace α] [MetricSpace β] (ρ : β → α) (hρ : Isometry ρ) (y : β)
    : (fun (x : α) ↦ iInf (fun z ↦ dist y z + dist x (ρ z))) = (fun (x : α) ↦ dist x (ρ y)) := by
    funext x
    refine le_antisymm ?_ ?_
    · refine csInf_le ?_ ⟨y, by simp only [dist_self, zero_add]⟩
      refine ⟨0, Set.mem_setOf.mpr ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact add_nonneg (dist_nonneg) (dist_nonneg)
    · apply le_csInf
      · refine ⟨dist x (ρ y), ⟨y, by simp only [dist_self, zero_add]⟩⟩
      · rintro _ ⟨z, hz, rfl⟩
        simp_rw [← hρ.dist_eq y z, dist_comm (ρ y) (ρ z), add_comm]
        exact dist_triangle x (ρ z) (ρ y)

theorem extend_self {α : Type*} [MetricSpace α] (f : E(α)) : extend (fun x ↦ x) isometry_id f = f := by
  simp [extend]
  by_cases hα : Nonempty α
  · ext x
    simp only [hα, ↓reduceDIte, coe_mk]
    apply min_point
  · simp only [hα, ↓reduceDIte]
    apply @emptymap_unique _ _ (not_nonempty_iff.mp hα) _ _



open Finset.Nonempty Function


theorem isfinsuppkatetov_extend {α β : Type*} [MetricSpace α][MetricSpace β]
  (ρ : β → α) (hρ : Isometry ρ) (f : E(β, ω)): extend ρ hρ f ∈ E(α, ω) := by
  by_cases hβ : Nonempty β
  · by_cases hα : Nonempty α
    · obtain ⟨_, _, ⟨s, rfl⟩, ⟨φ, rfl⟩⟩ := f
      by_cases hs : Nonempty s
      · set u := Finset.map ⟨ρ, hρ.injective⟩ s with u_def
        set ρ' : s → u := fun x ↦ by
          refine ⟨ρ x, ?_⟩
          simp only [u_def, Finset.mem_map]
          refine ⟨x, by simp only [Finset.coe_mem, Function.Embedding.coeFn_mk, and_self]⟩
        with ρ'_def
        have bij_ρ' : Function.Bijective ρ' := by
          rw [ρ'_def]
          constructor
          · intro x y hxy
            simp only [Subtype.mk.injEq ] at hxy
            apply Subtype.coe_injective <| hρ.injective hxy
          · rintro ⟨y, hy⟩
            simp only [u_def, Finset.mem_map] at hy
            obtain ⟨x, hx, rfl⟩ := hy
            refine ⟨⟨x, hx⟩, by simp only [Function.Embedding.coeFn_mk]⟩
        refine Set.mem_iUnion.mpr ⟨u, ?_⟩
        set φ' : u → ℝ := φ ∘ (Equiv.ofBijective ρ' bij_ρ').invFun with φ'_def
        have iskat_φ' : IsKatetov φ' := by
          constructor <;> (
            rintro ⟨x, hx⟩ ⟨y, hy⟩
            simp only [φ'_def, Equiv.invFun_as_coe, Function.comp_apply]
            obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_map.mp hx
            obtain ⟨y₁, hy₁, rfl⟩ :=  Finset.mem_map.mp hy
            simp only [Function.Embedding.coeFn_mk, Subtype.dist_eq, hρ.dist_eq]
            have h₁: (Equiv.ofBijective ρ' bij_ρ').symm ⟨ρ x₁, hx⟩ = ⟨x₁, hx₁⟩ := by
              apply (Equiv.symm_apply_eq (Equiv.ofBijective ρ' bij_ρ')).mpr
              simp only [Equiv.ofBijective_apply]
              congr
            have h₂: (Equiv.ofBijective ρ' bij_ρ').symm ⟨ρ y₁, hy⟩ = ⟨y₁, hy₁⟩ := by
              apply (Equiv.symm_apply_eq (Equiv.ofBijective ρ' bij_ρ')).mpr
              simp only [Equiv.ofBijective_apply]
              congr
            simp only [h₁, h₂])
          · apply (map_katetov φ).abs_sub_le_dist
          · apply (map_katetov φ).dist_le_add (Subtype.mk x₁ hx₁) (Subtype.mk y₁ hy₁)
        refine ⟨extend (fun (x : u) ↦ x) isometry_id ⟨φ', iskat_φ'⟩, ?_⟩
        · simp only [extend_self ⟨φ', iskat_φ'⟩]
          simp only [extend, nonempty_subtype, coe_mk, hα, ↓reduceDIte, hβ, hs]
          have  hu : Nonempty u := by aesop
          simp only [hu, ↓reduceDIte, mk.injEq]
          ext y
          obtain ⟨yₘ, hyₘ⟩ := @exists_eq_ciInf_of_finite _ _ _ _ _ (φ' + dist y ∘ (fun y' : u ↦ (y' : α)))
          rw [← hyₘ]
          simp only [Pi.add_apply, Function.comp_apply]
          have : iInf ((fun x => iInf ((φ : s → ℝ) + dist x ∘ (fun (x : s) => (x : β)))) + dist y ∘ ρ)
                = iInf ((φ : s → ℝ) + dist y ∘ (ρ ∘ fun x : s ↦ (x : β))) := by
            conv =>
              enter [-2, 1]
              rw [show (fun x => iInf ((φ : s → ℝ) + dist x ∘ fun (x : s) => (x : β))) + dist y ∘ ρ = (fun x ↦ (iInf ((φ : s → ℝ) + dist x ∘ (fun x : s ↦ (x : β ))) + (dist y (ρ x)))) by aesop]
            have : ∀ x : β, BddBelow (range ((φ : s → ℝ) + dist x ∘ fun (x₁ : s) => (x₁ : β))) := by
              intro x
              refine ⟨0, Set.mem_setOf.mpr ?_⟩
              rintro _ ⟨z, hz, rfl⟩
              apply add_nonneg katetov_nonneg dist_nonneg
            conv =>
              enter [-2, 1, x]
              rw [ciInf_add (this x) _]
            simp
            obtain ⟨xₘ, hxₘ⟩ := @exists_eq_ciInf_of_finite _ _ _ _ _ ((φ : s → ℝ) + dist y ∘ ρ ∘ fun (x₁ : s) => (x₁ : β))
            simp at hxₘ
            rw [show iInf ((φ : s → ℝ) + dist y ∘ ρ ∘ fun (x₁ : s) => (x₁ : β)) = ⨅ i, φ i + dist y (ρ i) by rfl]
            refine le_antisymm ?_ ?_
            · have : BddBelow (range fun x => ⨅ i, φ i + dist x ↑i + dist y (ρ x)) := by
                refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                simp
                apply le_ciInf
                intro x
                apply add_nonneg (add_nonneg katetov_nonneg dist_nonneg) dist_nonneg
              apply ciInf_le_of_le this xₘ
              have : BddBelow (range fun i => φ i + dist ↑xₘ ↑i + dist y (ρ ↑xₘ)) := by
                refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                apply add_nonneg (add_nonneg katetov_nonneg dist_nonneg) dist_nonneg
              apply ciInf_le_of_le this xₘ
              rw [← hxₘ]
              simp
            · apply le_ciInf
              intro x
              refine ciInf_mono ?_ ?_
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                apply add_nonneg katetov_nonneg dist_nonneg
              · intro x₂
                have :  dist y (ρ x₂) ≤ dist x x₂ + dist y (ρ x) := by
                  rw [add_comm]
                  rw [← hρ.dist_eq]
                  apply dist_triangle
                linarith
          set xₘ:=  ρ'.invFun yₘ
          rw [show yₘ = ρ' xₘ by simp [xₘ, Function.rightInverse_invFun bij_ρ'.surjective yₘ]] at *
          simp [φ'] at *
          rw [show ρ' xₘ = ρ xₘ by simp [ρ']] at *
          rw [this]
          rw [hyₘ]
          apply Equiv.iInf_congr (Equiv.ofBijective ρ' bij_ρ').symm
          rintro ⟨y, hy⟩
          simp
          congr
          simp [u] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          congr
          conv =>
            enter [-2, 1, 2, 1]
            rw [show ρ x = ρ' ⟨x, hx⟩ by simp [ρ']]
          simp
      · conv =>
          enter [2, 3]
          simp only [extend, hs, ↓reduceDIte, hβ]
        simp only [extend, hβ, ↓reduceDIte]
        conv =>
          enter [2, 1]
          tactic => convert (min_point₂ _ hρ _)
        simp_rw [dist_comm _ (ρ _)]
        apply isFinSuppKatetov_dist_point
    · simp only [extend, hβ, hα, ↓reduceDIte]
      have := (not_nonempty_iff.mp hα)
      simp only [← emptymap_unique (empty_katetovmap α)]
      rw [← empty_finsupp_eq_empty]
      simp only [Subtype.coe_prop]
  · simp only [extend, hβ]
    by_cases hα : Nonempty α
    · simp only [↓reduceDIte, hα, isFinSuppKatetov_dist_point]
    · simp only [hα, ↓reduceDIte]
      simp only [← @empty_finsupp_eq_empty _ _ (not_nonempty_iff.mp hα), Subtype.coe_prop]

theorem isometry_extend_finsupp {α β : Type*} [MetricSpace α][MetricSpace β]
  (ρ : β → α) (hρ : Isometry ρ) : Isometry (fun f : E(β, ω) ↦
    (⟨extend ρ hρ f, isfinsuppkatetov_extend ρ hρ f⟩ : E(α, ω))) := by
  by_cases hβ : Nonempty β
  · refine Isometry.of_dist_eq (fun f g ↦ le_antisymm ?_ ?_)
    · refine Real.iSup_le (fun x ↦ ?_) dist_nonneg
      simp [extend, hβ]
      have hpos : ∀ f : E(β, ω), BddBelow (Set.range ((f : β → ℝ) + dist x ∘ ρ)) := by
        refine fun f ↦ ⟨0, mem_lowerBounds.mpr ?_⟩
        rw [Set.forall_mem_range]
        refine fun x ↦ add_nonneg katetov_nonneg dist_nonneg
      have : (fun z ↦ (f : E(β)) z + dist x (ρ z)) - (fun z ↦ (g : E(β)) z + dist x (ρ z)) = fun z ↦ (f : E(β)) z - (g : E(β)) z := by
          aesop
      have hb : BddAbove (Set.range |(fun z ↦ (f : E(β)) z + dist x (ρ z)) - (fun z ↦ (g : E(β)) z + dist x (ρ z))|) := by
        simp_rw [this]
        exact bddAbove_range_abs_sub
      have := abs_sub_inf_le_sup (hpos f) (hpos g) hb
      refine le_trans this (?_)
      conv =>
        enter [1, 1, 1]
        tactic => simp_all only [Subtype.forall]
        rfl
      simp only [add_sub_add_right_eq_sub]
      exact le_refl _
    · refine Real.iSup_le ?_ dist_nonneg
      refine fun x ↦ ?_
      simp [extend, hβ]
      refine le_csSup_of_le bddAbove_range_abs_sub ⟨(ρ x), ?_⟩ (le_refl |(f : E(β)) x - (g : E(β)) x|)
      have : ∀ f : E(β), iInf (fun z ↦ (f : E(β)) z + dist (ρ x) (ρ z)) = f x:= by
        intro f; refine le_antisymm ?_ ?_
        · refine csInf_le ?_ ⟨x, by simp only [dist_self, add_zero]⟩
          refine ⟨0, Set.mem_setOf.mpr ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact add_nonneg (katetov_nonneg) (dist_nonneg)
        · apply le_csInf
          · refine ⟨f x + dist (ρ x) (ρ x), ⟨x, by simp only [dist_self, add_zero]⟩⟩
          · rintro _ ⟨z, hz, rfl⟩
            simp_rw [hρ.dist_eq]
            linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x z]
      simp
      conv =>
        enter [-2, 1, 1]
        tactic => convert (this f)
      conv =>
        enter [-2, 1, 2]
        tactic => convert (this g)
  · refine Isometry.of_dist_eq (fun f g ↦ ?_)
    simp [@emptyfinsuppmap_unique _ _ (not_nonempty_iff.mp hβ) f g]

theorem exists_isometry_finsupp (α β : Type) [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) :
  ∃ f : E(β, ω) → E(α, ω), Isometry f :=
  ⟨fun f ↦ ⟨extend ρ hρ f, isfinsuppkatetov_extend ρ hρ f⟩, isometry_extend_finsupp ρ hρ⟩


end KatetovExtension

open KatetovExtension KatetovMap DistPointEmbedding

instance instSeparableRange (α : Type*) [MetricSpace α] (s : Finset α) :
  IsSeparable (@range E(α) E(s) (KatetovExtension.extend (fun x ↦ ↑x) isometry_id)) := by
  have : SeparableSpace E(s) := by exact instSeparableSpaceKatetovMaps (by infer_instance)
  apply TopologicalSpace.isSeparable_range
  exact (isometry_extend (fun x : s ↦ (x : α)) isometry_id).continuous

instance instSeparableFinSuppKatetov (α : Type*) [MetricSpace α] [Countable α] :
    SeparableSpace E(α, ω) := by
  rw [KatetovExtension.FinSuppKatetovMaps]
  have := Set.countable_setOf_finite_subset (@Set.countable_univ α _)
  apply TopologicalSpace.IsSeparable.separableSpace
  apply TopologicalSpace.IsSeparable.iUnion (fun i ↦ @instSeparableRange α _ i)

set_option maxHeartbeats 1000000

open Classical in
noncomputable instance sepKat (α : Type*) [MetricSpace α] [SeparableSpace α] : SeparableSpace E(α, ω) := by
  by_cases hα : Nonempty α
  · obtain ⟨D, hDc, hdD⟩ := TopologicalSpace.exists_countable_dense α
    have : SeparableSpace E(D, ω) := @instSeparableFinSuppKatetov D _ hDc
    set ED := Set.range fun (f : E(D, ω)) ↦ (⟨extend (fun (x : D) ↦ (x : α)) (isometry_id) f, isfinsuppkatetov_extend (fun (x : D) ↦ (x : α)) isometry_id f⟩ : E(α, ω))
    have : Dense ED := by
      rw [Metric.dense_iff]
      intro f ε εpos
      set f' := f with f'_def
      obtain ⟨f'' : E(α), hf''⟩ := f'
      obtain ⟨_, _, ⟨s, rfl⟩, ⟨φ, rfl⟩⟩ := f
      have  : ∀ x : α, ∃ x' : D, dist x x' < ε/4 := by
          intro x
          obtain ⟨x', hx', hxε⟩ := Dense.exists_dist_lt hdD x (show ε/4 > 0 by linarith)
          refine ⟨⟨x', hx'⟩, hxε⟩
      choose ρ hρ using this
      by_cases hs : Nonempty s
      · set s' : Finset D := Finset.image ρ s
        set g : E(s') := by
          refine ⟨fun x ↦ f'' x, ?_⟩
          constructor
          · intro x y
            exact (map_katetov f'').abs_sub_le_dist (x : α) y
          · intro x y
            exact (map_katetov f'').dist_le_add (x : α) y
        have hg : g ∈ E(s', ω) := by
          simp [FinSuppKatetovMaps]
          set t : Finset s' := {x | x : s'}
          use t
          have : IsKatetov fun (x : t) ↦ g (x : s') := by
            constructor
            · exact fun x y ↦ (map_katetov g).abs_sub_le_dist (x : s') y
            · exact fun x y ↦ (map_katetov g).dist_le_add (x : s') y
          use (⟨fun (x : t) ↦ g (x : s'), this⟩)
          simp [extend]
          have h : ∃ a, ∃ (b : a ∈ D) (b_1 : ⟨a, b⟩ ∈ s'), ⟨⟨a, b⟩, b_1⟩ ∈ t := by
            aesop
          simp [h]
          ext x
          simp only [coe_mk]
          refine le_antisymm ?_ ?_
          · refine ciInf_le_of_le ?_ ⟨x, by aesop⟩ ?_
            · refine ⟨0, Set.mem_setOf.mpr ?_⟩
              rintro _ ⟨z, hz, rfl⟩
              exact add_nonneg (katetov_nonneg) (dist_nonneg)
            · simp
          · have : Nonempty t := by
              use x
              aesop
            apply le_ciInf
            · intro x'
              simp
              suffices g x - g x' ≤ dist x x' by linarith
              linarith [le_of_abs_le <| (map_katetov g).abs_sub_le_dist x x']
        set g' : E(D, ω) := ⟨extend (fun (x : s') ↦ (x : D)) isometry_id g, isfinsuppkatetov_extend _ _ ⟨g, hg⟩⟩
        set g'' : E(α, ω) := ⟨extend (fun (x : D) ↦ (x : α)) isometry_id g', isfinsuppkatetov_extend (fun (x : D) ↦ (x : α)) isometry_id g'⟩
        refine ⟨g'', ?_⟩
        constructor
        · rw [Metric.mem_ball]
          simp [dist]
          refine lt_of_le_of_lt ?_ (show ε/2 < ε by linarith)
          apply ciSup_le
          intro x₀
          simp only [Pi.abs_apply, Pi.sub_apply]
          have hD: ∃ a, a ∈ D := by
              use (ρ x₀)
              simp only [Subtype.coe_prop, ED]
          have hnD : Nonempty D := by aesop
          have h : ∃ a, ∃ (b : a ∈ D), ⟨a, b⟩ ∈ s' := by
            aesop
          have hle : ∀ x, f'' x ≤ (g'' : α → ℝ) x := by
            intro x
            unfold g''
            simp
            simp [extend, hD]
            rw [Pi.add_def]
            simp
            unfold g'
            simp [extend, h]
            simp_rw [Pi.add_def (g : s' → ℝ) _]
            simp
            have : Nonempty { x // x ∈ s' } := by aesop
            have : ∀ i : D, BddBelow (range fun i_1 ↦ g i_1 + dist i ↑i_1) := by
              intro i
              refine ⟨0, Set.mem_setOf.mpr ?_⟩
              rintro _ ⟨z, hz, rfl⟩
              exact add_nonneg (katetov_nonneg) (dist_nonneg)
            conv =>
              rhs
              arg 1
              intro i
              rw [ciInf_add (this i)]
            have :  ⨅ i : D, ⨅ i_1, g i_1 + dist x ↑i_1 ≤  ⨅ i : D, ⨅ i_1, g i_1 + dist i ↑i_1 + dist x ↑i := by
              apply ciInf_mono
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                simp
                apply le_ciInf
                intro _
                exact add_nonneg (katetov_nonneg) (dist_nonneg)
              · intro i
                apply ciInf_mono
                · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                  rintro _ ⟨z, hz, rfl⟩
                  exact add_nonneg (katetov_nonneg) (dist_nonneg)
                · intro i_1
                  rw [add_assoc]
                  gcongr
                  rw [add_comm]
                  apply dist_triangle
            refine le_trans ?_ this
            unfold g
            simp
            have : f'' = extend (fun x ↦ ↑x) isometry_id φ  := by aesop
            rw [this]
            simp [extend]
            have : ∃ x, x ∈ s := by
              obtain ⟨x, hx⟩ := hs
              refine ⟨x, hx⟩
            simp [this]
            have : ∀ i_1 : s', BddBelow (range fun i ↦ φ i + dist (i_1 : α) i) := by
              intro i
              refine ⟨0, Set.mem_setOf.mpr ?_⟩
              rintro _ ⟨z, hz, rfl⟩
              exact add_nonneg (katetov_nonneg) (dist_nonneg)
            conv =>
              rhs
              arg 1
              intro i_1
              lhs
              arg 1
              rw [Pi.add_def]
            conv =>
              rhs
              arg 1
              intro i_1
              simp
              rw [ciInf_add (this i_1)]
            have :  ⨅ i_1 : s', ⨅ i, φ i + dist x ↑i ≤ ⨅ i_1 : s', ⨅ i, φ i + dist (i_1 : α) ↑i + dist x ↑↑i_1:= by
              apply ciInf_mono
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                apply le_ciInf
                intro _
                exact add_nonneg (katetov_nonneg) (dist_nonneg)
              · intro i
                apply ciInf_mono
                · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                  rintro _ ⟨z, hz, rfl⟩
                  exact add_nonneg (katetov_nonneg) (dist_nonneg)
                · intro i_1
                  rw [add_assoc]
                  gcongr
                  rw [add_comm]
                  apply dist_triangle
            refine le_trans ?_ this
            rw [ciInf_const]
            exact_mod_cast le_rfl
          have hsε : ∀ x : s, |(g'' : α → ℝ) x - f'' x| ≤ ε/2 := by
            intro x
            calc
            _ =
              |((g'' : α → ℝ) x - (g'' : α → ℝ) (ρ x)) + ((g'' : α → ℝ) (ρ x) - f'' (ρ x)) + (f'' (ρ x) - f'' x)| :=  by ring_nf
            _ ≤  |(g'' : α → ℝ) x - (g'' : α → ℝ) (ρ x)| + |(g'' : α → ℝ) (ρ x) - f'' (ρ x)| + |f'' (ρ x) - f'' x| := by
              repeat apply (abs_add ..).trans; gcongr; try exact abs_add _ _
            _ ≤ dist (x : α) (ρ x) + |(g'' : α → ℝ) (ρ x) - f'' (ρ x)| + dist (x : α) (ρ x) := by
              have := (map_katetov (g'' : E(α))).abs_sub_le_dist (x : α) (ρ x)
              have := (map_katetov (f'' : E(α))).abs_sub_le_dist (x : α) (ρ x)
              rw [abs_sub_comm] at this
              linarith
            _ ≤ ε/2 + |(g'' : α → ℝ) (ρ x) - f'' (ρ x)| := by
                linarith [hρ x]
            _ = ε/2 + 0:= by
              congr
              unfold g''
              simp [extend]
              simp [hD]
              have : iInf ((g' : D → ℝ) + dist ((ρ x) : α) ∘ fun (x : D) ↦ (x : α)) = (g' : D → ℝ) (ρ x) := by
                refine le_antisymm ?_ ?_
                · apply ciInf_le_of_le ?_ ⟨ρ x, by aesop⟩ ?_
                  · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                    rintro _ ⟨z, hz, rfl⟩
                    exact add_nonneg (katetov_nonneg) (dist_nonneg)
                  · simp
                · have : Nonempty D := by exact Nonempty.to_subtype hD
                  apply le_ciInf
                  intro a
                  simp
                  have := le_of_abs_le <| (map_katetov (g' : E(D))).abs_sub_le_dist (ρ x) a
                  suffices (g' : E(D)) (ρ ↑x) - (g' : E(D)) a ≤  dist ((ρ ↑x) : α) (a : α) by linarith
                  exact this
              rw [this]
              unfold g'
              simp [extend]
              simp [h]
              have hxs : ρ x ∈ s' := by
                unfold s'
                obtain ⟨x, hx⟩ := x
                aesop
              have : iInf ((g : s' → ℝ) + dist (ρ x)  ∘ fun (x : s') ↦ (x : D)) = (g : s' → ℝ) ⟨ρ x, hxs⟩ := by
                refine le_antisymm ?_ ?_
                · apply ciInf_le_of_le ?_ ⟨ρ x, by aesop⟩ ?_
                  · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                    rintro _ ⟨z, hz, rfl⟩
                    exact add_nonneg (katetov_nonneg) (dist_nonneg)
                  · simp
                · have : Nonempty s' := by aesop
                  apply le_ciInf
                  intro a
                  simp
                  have := le_of_abs_le <| (map_katetov g).abs_sub_le_dist ⟨ρ ↑x, hxs⟩ a
                  rw [show  dist ⟨ρ ↑x, hxs⟩ a = dist (ρ x) a by aesop] at this
                  suffices g ⟨ρ ↑x, hxs⟩ - g a ≤  dist ((ρ ↑x) : α) (a : α) by linarith
                  exact this
              rw [this]
              unfold g
              simp
            _ ≤ ε/2 := by norm_num
          have hge : ∀ x, (g'' : α → ℝ) x - ε/2 ≤ f'' x := by
            have hf'' : f'' = extend (fun x ↦ ↑x) isometry_id φ  := by aesop
            rw [hf'']
            simp [extend]
            have : ∃ x, x ∈ s := by
              obtain ⟨x, hx⟩ := hs
              refine ⟨x, hx⟩
            simp [this]
            have : ∀ x : s, φ x = f'' x := by
              intro xₛ
              rw [hf'']
              simp [extend]
              simp [this]
              refine le_antisymm ?_ ?_
              · apply le_ciInf
                intro x'
                have := le_of_abs_le <| (map_katetov φ).abs_sub_le_dist xₛ x'
                simp
                rw [show dist (xₛ : α) x' = dist xₛ x' by exact rfl]
                linarith
              · have : Nonempty s' := by aesop
                apply ciInf_le_of_le ?_ xₛ (by simp)
                refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                exact add_nonneg (katetov_nonneg) (dist_nonneg)
            conv =>
              enter [i, -1, 1, 1]
              rw [Pi.add_def]
              intro xₛ
              rw [this]
            intro x
            have : ∀ x : s, (g'' : α → ℝ) x ≤ f'' x + ε/2 := by
              intro x
              have := le_of_abs_le (hsε x)
              linarith
            simp
            have : (⨅ xₛ : s, (g'' : α → ℝ) ↑xₛ - ε/2 + (dist x xₛ)) ≤ (⨅ xₛ : s, f'' ↑xₛ + (dist x xₛ)) := by
              apply ciInf_mono
              · refine ⟨-ε/2, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                simp
                suffices h : 0 ≤ (g'' : α → ℝ) z + dist x z by linarith
                exact add_nonneg (katetov_nonneg) (dist_nonneg)
              · intro x'
                gcongr
                linarith [this x']
            suffices  (g'' : α → ℝ) x  - ε/2 ≤ (⨅ xₛ : s, f'' ↑xₛ + dist x ↑xₛ) by linarith
            apply le_trans ?_ this
            apply le_ciInf
            intro x'
            suffices  (g'' : α → ℝ) x -  (g'' : α → ℝ) x' ≤ dist x x' by linarith
            exact le_of_abs_le <| (map_katetov (g'' : E(α))).abs_sub_le_dist x x'
          specialize hge x₀
          specialize hle x₀
          rw [abs_le]
          constructor <;> linarith

        · simp only [mem_range, Subtype.mk.injEq, exists_apply_eq_apply, ED, g'']
      · rw [f'_def]
        have : IsEmpty s := by exact not_nonempty_iff.mp hs
        have : ¬ ∃ x, x ∈ s := by aesop
        conv =>
          enter [1, 1, 1]
          simp only [extend, nonempty_subtype, Real.iInf_of_isEmpty, ED]
          simp only [this, ↓reduceDIte, ED]
          simp only [hα, ↓reduceDIte, ED]
        set x₀ :=  Classical.choice hα with x₀_def
        set g' : E(D, ω) := ⟨⟨fun (y : D) ↦ dist (ρ x₀) y, isKatetov_dist_point (ρ x₀)⟩, isFinSuppKatetov_dist_point _⟩
        set g'' : E(α, ω) := ⟨extend (fun (x : D) ↦ (x : α)) isometry_id g', isfinsuppkatetov_extend (fun (x : D) ↦ (x : α)) isometry_id g'⟩
        refine ⟨g'', ?_⟩
        constructor
        · rw [Metric.mem_ball]
          simp only [dist, coe_mk, ED]
          refine lt_of_le_of_lt ?_ (show ε/2 < ε by linarith)
          apply ciSup_le
          intro x
          unfold g''
          simp only [Pi.abs_apply, Pi.sub_apply, ED]
          unfold g'
          simp only [ED]
          simp only [extend, nonempty_subtype, coe_mk, ED]
          have hD : ∃ a, a ∈ D := by
            use (ρ x)
            simp only [Subtype.coe_prop, ED]
          simp only [hD, ↓reduceDIte, coe_mk, ge_iff_le, ED]
          have : iInf ((dist x ∘ fun (x : D) ↦ (x : α)) + fun y ↦ dist (ρ x₀) y) = dist x (ρ x₀) := by
            refine le_antisymm ?_ ?_
            · apply ciInf_le_of_le ?_ ⟨ρ x₀, by aesop⟩ ?_
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                exact add_nonneg (dist_nonneg) (dist_nonneg)
              · simp
            · have : Nonempty D := by exact Nonempty.to_subtype hD
              apply le_ciInf
              intro a
              simp only [Pi.add_apply, Function.comp_apply, ED]
              rw [dist_comm (ρ x₀)]
              exact dist_triangle x a (ρ x₀)
          conv =>
            enter [-2, 1, 1]
            rw [add_comm]
            rw [this]
          rw [dist_comm x, x₀_def]
          specialize hρ x₀
          have := abs_dist_sub_le ((ρ x₀) : α) x₀ x
          apply le_trans this
          rw [dist_comm]
          linarith
        · simp only [mem_range, Subtype.mk.injEq, exists_apply_eq_apply, ED, g'']
    rw [← Dense.isSeparable_iff this]
    apply TopologicalSpace.isSeparable_range (isometry_extend_finsupp (fun (x : D) ↦ (x : α)) (isometry_id)).continuous
  · simp only [not_nonempty_iff] at hα
    exact instSeparableFinSuppKatetov α

end KatetovMap

open KatetovMap KatetovExtension TopologicalSpace

universe u
-- set_option trace.Meta.synthInstance true
noncomputable def Aux (α : Type*) [inst : MetricSpace α] : ℕ → Σ (β : Type _), MetricSpace β := fun n ↦
  match n with
  | 0 => ⟨α, inst⟩
  | n + 1 => by
    have : MetricSpace ((Aux α n).1) := (Aux α n).2
    exact ⟨E((Aux α n).1, ω), by infer_instance⟩

noncomputable def X (α : Type*) [MetricSpace α] : ℕ → Type _ := fun n ↦ (Aux α n).1

noncomputable instance is_metricXn (α : Type*) [MetricSpace α] (n : ℕ) :
    MetricSpace (X α n) := (Aux α n).2

noncomputable instance is_sepXn (α : Type*) [MetricSpace α] [SeparableSpace α] (n : ℕ) :
    SeparableSpace (X α n) := by
    unfold X
    induction' n with n ih
    · simp [Aux]
      infer_instance
    · simp [Aux]
      refine @sepKat ((Aux α n).1) (Aux α n).2 ih


noncomputable def f (α : Type u) [MetricSpace α]: (n : ℕ) → (X α n) → X α (n+1) :=
  fun n ↦ (distPointEmbeddingFinsuppKatetov (X α n))

theorem I (α : Type*) [MetricSpace α]: ∀ (n : ℕ), Isometry (f α n) := by
  intro n; unfold f; exact (distPointEmbeddingFinsuppKatetov.isometry (X α n))


def UrysohnSpace (α : Type*) [MetricSpace α] : Type _ :=
  UniformSpace.Completion (Metric.InductiveLimit (I α))

noncomputable instance : MetricSpace (UrysohnSpace α) := by
  unfold UrysohnSpace
  apply UniformSpace.Completion.instMetricSpace

instance (α : Type*) [MetricSpace α] : CompleteSpace (UrysohnSpace α) := by
  unfold UrysohnSpace
  infer_instance

theorem UrysohnSeparable (α : Type*) [MetricSpace α] [SeparableSpace α]
    : SeparableSpace (UrysohnSpace α) := by
    unfold UrysohnSpace
    refine @UniformSpace.Completion.separableSpace_completion _ _ ?_
    refine @separableInductiveLimit_of_separable _ _ ?_ _ (I α)
    apply is_sepXn
