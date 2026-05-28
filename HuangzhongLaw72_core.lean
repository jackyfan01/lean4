/-
  黄钟还原术72律 — 核心定理在线验证版
  适用于 https://live.lean-lang.org

  复制此文件全部内容，等待约 2 分钟 Mathlib4 加载后查看结果
  最后两行 #check 无红色下划线即表示验证通过
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Field.Basic

-- ============================================================
-- 核心定义
-- ============================================================

/-- (2n+1)!! 双阶乘 -/
def doubleFactOdd : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * (n + 1) + 1) * doubleFactOdd n

/-- π-e交替级数通项 -/
noncomputable def piE_term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (doubleFactOdd n : ℝ)

-- ============================================================
-- 关键引理
-- ============================================================

theorem doubleFactOdd_pos (n : ℕ) : 0 < doubleFactOdd n := by
  induction n with
  | zero => unfold doubleFactOdd; omega
  | succ n ih => unfold doubleFactOdd; exact Nat.mul_pos (by omega) ih

theorem doubleFactOdd_ge_pow3 (n : ℕ) : 3 ^ n ≤ doubleFactOdd n := by
  induction n with
  | zero => simp [doubleFactOdd]
  | succ n ih =>
    unfold doubleFactOdd
    calc 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≤ 3 * doubleFactOdd n := Nat.mul_le_mul_left 3 ih
      _ ≤ (2 * (n + 1) + 1) * doubleFactOdd n :=
          Nat.mul_le_mul_right (doubleFactOdd n) (by omega)

theorem pow3_cast_pos (n : ℕ) : (0 : ℝ) < (3 : ℝ) ^ n :=
  pow_pos (by norm_num : (0 : ℝ) < 3) n

-- ============================================================
-- 核心定理1: 通项绝对值上界
-- ============================================================

theorem piE_term_norm_le (n : ℕ) : ‖piE_term n‖ ≤ (1 / 3 : ℝ) ^ n := by
  unfold piE_term
  have hdf : (0 : ℝ) < (doubleFactOdd n : ℝ) :=
    Nat.cast_pos.mpr (doubleFactOdd_pos n)
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast, one_div, inv_pow]
  apply inv_le_inv_of_le (pow3_cast_pos n)
  exact_mod_cast doubleFactOdd_ge_pow3 n

-- ============================================================
-- 核心定理2: 绝对收敛
-- ============================================================

private def geom13 : ℕ → ℝ := fun n => (1 / 3 : ℝ) ^ n

private theorem geom13_summable : Summable geom13 :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem piE_series_summable : Summable piE_term :=
  geom13_summable.of_norm_bounded piE_term_norm_le

-- ============================================================
-- 辅助: 范数可求和
-- ============================================================

theorem piE_norm_summable : Summable (fun n => ‖piE_term n‖) :=
  geom13_summable.of_norm_bounded (fun n => by rw [norm_norm]; exact piE_term_norm_le n)

theorem geom_tail_summable (k : ℕ) : Summable (fun n => (1 / 3 : ℝ) ^ (n + k)) :=
  geom13_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem piE_tail_summable (k : ℕ) : Summable (fun n => piE_term (n + k)) :=
  piE_series_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem piE_tail_norm_summable (k : ℕ) : Summable (fun n => ‖piE_term (n + k)‖) :=
  (geom_tail_summable k).of_norm_bounded (fun n => by
    rw [norm_norm]; exact piE_term_norm_le (n + k))

-- ============================================================
-- 核心定理3: 6项截断误差
-- ============================================================

noncomputable def partialSum_piE_real (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), piE_term n

noncomputable def piE_limit : ℝ := ∑' n, piE_term n

theorem truncation_6_approx :
    ‖partialSum_piE_real 5 - piE_limit‖ ≤ (1 / 3 : ℝ) ^ 5 / 2 := by
  unfold partialSum_piE_real piE_limit
  -- 分解: ∑' f = ∑_{<6} f + ∑' f(·+6)
  have hdecomp := (sum_add_tsum_nat_add 6 piE_series_summable).symm
  -- S_5 - L = -(尾部)
  have hdiff : ∑ n ∈ Finset.range 6, piE_term n - ∑' n, piE_term n =
      -(∑' n, piE_term (n + 6)) := by linarith [hdecomp]
  rw [hdiff, norm_neg]
  calc ‖∑' n, piE_term (n + 6)‖
      ≤ ∑' n, ‖piE_term (n + 6)‖ :=
          norm_tsum_le_tsum_norm (piE_tail_norm_summable 6)
    _ ≤ ∑' n, (1 / 3 : ℝ) ^ (n + 6) :=
          tsum_le_tsum (fun n => piE_term_norm_le (n + 6))
            (piE_tail_norm_summable 6) (geom_tail_summable 6)
    _ = (1 / 3) ^ 6 * ∑' n, (1 / 3 : ℝ) ^ n := by
          simp_rw [pow_add]; rw [tsum_mul_left]
    _ = (1 / 3) ^ 6 * (3 / 2) := by
          congr 1; exact tsum_geometric_of_lt_one (by norm_num) (by norm_num)
    _ = (1 / 3) ^ 5 / 2 := by ring

-- ============================================================
-- 验证: 无红色下划线即通过
-- ============================================================

#check @piE_series_summable   -- piE_series_summable : Summable piE_term
#check @truncation_6_approx   -- ‖partialSum_piE_real 5 - piE_limit‖ ≤ (1/3)^5/2
