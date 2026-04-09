> [!quote] E. B. Christoffel，1870
> 我所得到的关于多边形的结论，可以在相当一般的条件下进行推广。研究这一问题，是因为它是深入理解映射理论的关键一步。自黎曼的学位论文问世以来，这一方向的进展十分有限，而映射理论与黎曼函数论基本定理之间的紧密联系，都非常值得进一步深入研究。

本章讨论的问题与思想相比前几章更具几何色彩。我们主要关注全纯函数的映射性质，并且本章的大部分结论都是全局性的，而非前三章那种局部性的分析结果。贯穿本章的核心动机来自下面这个基本问题：

**给定 $\mathbb{C}$ 中的两个开集 $U$ 和 $V$，是否存在它们之间的全纯双射？**

所谓全纯双射，指的是同时满足全纯与双射的函数。可以证明，其逆映射也自动全纯。如果存在这样的映射，我们就能把一个区域上的解析函数问题，转移到结构更简单、性质更优良的区域上研究。最典型的选择是取 $V = \mathbb{D}$ 为单位圆盘，其上已经有非常完善的解析函数理论。于是我们自然提出更具体的问题：

**给定 $\mathbb{C}$ 的开子集 $\Omega$，$\Omega$ 满足什么条件时，存在从 $\Omega$ 到单位圆盘 $\mathbb{D}$ 的全纯双射？**
  
本章主要内容如下：

- 首先构造显式共形映射，例如用分式线性变换将上半平面映为单位圆盘，并通过复合有理函数、三角函数、对数函数等得到更多例子，同时应用这些映射求解特定区域上 Laplace 方程的 Dirichlet 问题。
- 其次证明 Schwarz 引理，并利用它刻画单位圆盘到自身的所有全纯自同构，这些自同构同样由分式线性变换给出。
- 本章核心为 Riemann 映射定理：若 $\Omega$ 是单连通区域且 $\Omega \neq \mathbb{C}$，则 $\Omega$ 可全纯双射地映到单位圆盘，该定理对区域边界 $\partial\Omega$ 几乎不要求光滑性。
- 最后一节给出多边形区域的显式映射公式，即 Schwarz–Christoffel 公式；其中矩形对应的映射由椭圆积分给出，并由此引出双周期函数，这也是 19 世纪复分析的重要研究主题。

# 1. 共形等价与例子

我们先给出本章会反复使用的基本定义。

> [!definition] 共形映射（双全纯映射）
> 如果一个双射全纯函数 $f: U \to V$ 既是全纯又是双射，则称 $f$ 为**共形映射**，也称为**双全纯映射**。
>
> 若存在这样的映射 $f$，就称区域 $U$ 与 $V$ **共形等价**，或简称**双全纯等价**。
一个关键性质是：共形映射的逆映射也自动是全纯的。

> [!proposition] 
> 如果 $f: U \to V$ 全纯且单射，则对任意 $z \in U$ 都有 $f'(z) \neq 0$。
> 
> 特别地，$f$ 在其像集上的逆映射也是全纯的，即共形映射的逆仍是共形映射。

> [!proof]-
> **采用反证法**。假设存在 $z_0 \in U$ 使得 $f'(z_0) = 0$，则在 $z_0$ 附近可将 $f$ 展开为
> $$
> f(z) - f(z_0) = a(z - z_0)^k + G(z),
> $$
> 其中 $a \neq 0$，$k \ge 2$，而 $G(z)$ 在 $z_0$ 处至少有 $k+1$ 阶零点。
>
> 对模长充分小的 $w\ne 0$，令 $F(z) \coloneqq a(z - z_0)^k - w$, 则
> $$
> f(z) - f(z_0) - w = F(z) + G(z).
> $$
> 在以 $z_0$ 为中心的充分小圆周上，有 $|G(z)| < |F(z)|$。因为 $F(z)$ 在圆内至少有两个不同零点，由 [Rouché 定理](#^rouche-theorem) 可知，$f(z) - f(z_0) - w$ 在该圆内也至少有两个不同零点。
>
> 另一方面，在 $z_0$ 附近且 $z \neq z_0$ 处有 $f'(z) \neq 0$，因此这两个零点互不相同，这与 $f$ 是单射矛盾。
>
> 接下来记逆映射 $g = f^{-1}$。任取 $w_0 \in V$，并设 $w$ 充分接近 $w_0$，令 $w = f(z)$，$w_0 = f(z_0)$。当 $w \neq w_0$ 时，
> $$
> \frac{g(w) - g(w_0)}{w - w_0} = \frac{1}{\dfrac{f(z) - f(z_0)}{z - z_0}}.
> $$
> 因为已经证明 $f'(z_0) \neq 0$，令 $z \to z_0$ 即可知 $g$ 在 $w_0$ 处全纯，且
> $$
> g'(w_0) = \frac{1}{f'(g(w_0))}.
> $$

由此命题可知，两个开集 $U$ 和 $V$ 共形等价当且仅当存在全纯函数 $f: U \to V$ 与 $g: V \to U$，使得对所有 $z \in U$ 和 $w \in V$ 成立
$$
g(f(z)) = z,\quad f(g(w)) = w.
$$

> [!theorem] Rouché 定理
> 设 $f$ 和 $g$ 在包含圆周 $C$ 及其内部的开集 $\Omega$ 上全纯。若对 $C$ 上所有 $z$ 有
> $$
> |g(z)| < |f(z)|,
> $$
> 则 $f + g$ 和 $f$ 在 $C$ 内部具有相同个数的零点（计数重数）。
>   
> ^rouche-theorem

> [!note] 术语说明
> 需要说明的是，本章使用的术语在文献中并不完全统一。
>
> 有些作者将满足 $f'(z) \neq 0$（对所有 $z \in U$）的全纯映射 $f: U \to V$ 直接称为**共形映射**。
> 这一定义比我们采用的定义更宽松；例如，在去心圆盘 $\mathbb{C} \setminus \{0\}$ 上的函数 $f(z) = z^2$ 满足 $f'(z) \neq 0$，但并非单射。
>
> 不过，条件 $f'(z) \neq 0$ 等价于 $f$ 是局部双射（见习题 1）。
> 该条件有一个重要的几何意义，这也是不同文献对“共形”定义存在差异的原因：满足 $f'(z) \neq 0$ 的全纯映射**保持角度**。
>
> 粗略地讲，如果两条曲线 $\gamma$ 与 $\eta$ 在 $z_0$ 处相交，且它们切向量的有向夹角为 $\alpha$，那么像曲线 $f \circ \gamma$ 与 $f \circ \eta$ 在 $f(z_0)$ 处相交，且切向量之间仍形成相同的夹角 $\alpha$。
> 习题 2 会进一步说明这一结论。

下面我们通过一系列具体例子展开共形映射的讨论。
第一个例子给出单位圆盘与上半平面之间的共形等价关系，它在很多问题中都起着关键作用。

## 圆盘与上半平面

我们将上半平面记作 $\mathbb{H}$，它由所有虚部为正的复数构成，即
$$
\mathbb{H} = \{z \in \mathbb{C}: \operatorname{Im}(z) > 0\}.
$$
一个看似出乎意料却十分重要的结论是：无界区域 $\mathbb{H}$ 与单位圆盘 $\mathbb{D}$ 是共形等价的，并且可以写出显式的共形映射。

定义映射
$$
F(z) = \frac{i - z}{i + z}, \qquad G(w) = i \cdot \frac{1 - w}{1 + w}.
$$

> [!theorem] 
> 映射 $F: \mathbb{H} \to \mathbb{D}$ 是共形映射，其逆映射为 $G: \mathbb{D} \to \mathbb{H}$。

> [!proof]-
> 首先，$F$ 和 $G$ 在各自定义域内都是全纯函数。
> 对于任意 $z \in \mathbb{H}$，它到点 $i$ 的距离小于到 $-i$ 的距离，因此 $|F(z)| < 1$，即 $F$ 将 $\mathbb{H}$ 映入单位圆盘 $\mathbb{D}$。
>
> 接下来验证 $G$ 将 $\mathbb{D}$ 映入 $\mathbb{H}$。
> 设 $w = u + iv \in \mathbb{D}$，直接计算虚部可得
> $$
> \operatorname{Im}(G(w))
> = \operatorname{Re}\!\left(\frac{1 - u - iv}{1 + u + iv}\right)
> = \frac{1 - u^2 - v^2}{(1 + u)^2 + v^2} > 0,
> $$
> 其中不等号由 $|w| < 1$ 保证，因此 $G(w) \in \mathbb{H}$。
>
> 最后验证互逆关系：
> $$
> F(G(w)) = \frac{i - i \frac{1 - w}{1 + w}}{i + i \frac{1 - w}{1 + w}}
> = \frac{(1 + w) - (1 - w)}{(1 + w) + (1 - w)} = w,
> $$
> 同理可证 $G(F(z)) = z$。定理得证。

这组映射在区域边界上的行为也很有代表性。
$F$ 除 $z = -i$ 外在复平面上处处全纯，特别地，它在 $\mathbb{H}$ 的边界（实直线 $\mathbb{R}$）上连续。
对任意实数 $z = x$，$x$ 到 $i$ 与到 $-i$ 的距离相等，故 $|F(x)| = 1$，即 $F$ 把实轴映到单位圆周。

将 $F(x)$ 展开为
$$
F(x) = \frac{i - x}{i + x}
= \frac{1 - x^2}{1 + x^2} + i \cdot \frac{2x}{1 + x^2},
$$
再用 $x = \tan t$（$t \in (-\pi/2, \pi/2)$）参数化实轴，利用三角恒等式
$$
\cos 2t = \frac{1 - \tan^2 t}{1 + \tan^2 t}, \quad
\sin 2t = \frac{2\tan t}{1 + \tan^2 t},
$$
可得 $F(x) = e^{i2t}$。
这说明：实轴在 $F$ 下的像为单位圆周去掉点 $-1$；
当 $x$ 从 $-\infty$ 到 $\infty$ 变动时，$F(x)$ 从 $-1$ 出发，沿圆周先经过下半圆弧。

单位圆周上的点 $-1$ 对应上半平面的“无穷远点”。

> [!remark] 分式线性变换
> 形如
> $$
> z \mapsto \frac{az + b}{cz + d}
> $$
> 的映射（其中 $a,b,c,d$ 为复数，且分母不是分子的常数倍）称为**分式线性变换**。
> 定理 2.1 和 2.4 中出现的圆盘与上半平面的自同构，都是分式线性变换的典型例子。

## 更多例子 ^further-examples

我们在这里收集几个共形映射的示例。在某些情况下，我们讨论映射在相关区域边界上的行为。图中展示了其中的一些映射。

> [!example] 平移与伸缩 ^ex-translation-dilation
> 平移与伸缩提供了第一批简单的例子。事实上，若 $h \in \mathbb{C}$，平移 $z \mapsto z + h$ 是从 $\mathbb{C}$ 到自身的共形映射，其逆为 $w \mapsto w - h$。若 $h$ 是实数，则该平移也是从上半平面到自身的共形映射。
>
> 对于任意非零复数 $c$，映射 $f: z \mapsto cz$ 是从复平面到自身的共形映射，其逆就是 $g: w \mapsto c^{-1}w$。若 $c$ 的模为 $1$，即 $c = e^{i\varphi}$（$\varphi \in \mathbb{R}$），则 $f$ 是旋转 $\varphi$ 角。若 $c > 0$，则 $f$ 对应一个伸缩。最后，若 $c < 0$，映射 $f$ 由伸缩 $|c|$ 再旋转 $\pi$ 复合而成。

> [!example] 幂函数 ^ex-power-function
> 若 $n$ 是正整数，则映射 $z \mapsto z^{n}$ 是从扇形 $S = \{z \in \mathbb{C} : 0 < \arg(z) < \pi / n\}$ 到上半平面的共形映射。该映射的逆就是 $w \mapsto w^{1/n}$，按对数主支定义。
>
> 更一般地，若 $0 < \alpha < 2$，映射 $f(z) = z^{\alpha}$ 将上半平面映为扇形 $S = \{w \in \mathbb{C} : 0 < \arg(w) < \alpha \pi\}$。事实上，若我们选取去掉正实轴所得到的对数分支，并令 $z = re^{i\theta}$（$r > 0$，$0 < \theta < \pi$），则
> $$
> f(z) = z^{\alpha} = |z|^{\alpha} e^{i\alpha\theta}.
> $$
> 因此，$f$ 将 $\mathbb{H}$ 映到 $S$ 中。此外，容易验证 $f$ 的逆由 $g(w) = w^{1/\alpha}$ 给出，其中对数分支选取使得 $0 < \arg w < \alpha \pi$。
>
> 将刚刚讨论的映射与 [[#^ex-translation-dilation|示例 1]] 中的平移和旋转复合，我们可以将上半平面共形地映到 $\mathbb{C}$ 中的任意（无限）扇形。
>
> 我们注意到 $f$ 的边界行为。若 $x$ 在实轴上从 $-\infty$ 走到 $0$，则 $f(x)$ 在由 $\arg z = \alpha \pi$ 确定的射线上从 $\infty e^{i\alpha \pi}$ 走到 $0$。当 $x$ 在实轴上从 $0$ 走到 $\infty$ 时，像 $f(x)$ 也在实轴上从 $0$ 走到 $\infty$。

> [!example] 上半圆盘到第一象限 ^ex-half-disc-to-first-quadrant
> 映射 $f(z) = \dfrac{1 + z}{1 - z}$ 将上半圆盘 $\{z = x + iy : |z| < 1 \text{ 且 } y > 0\}$ 共形地映到第一象限 $\{w = u + iv : u > 0 \text{ 且 } v > 0\}$。事实上，若 $z = x + iy$，则
> $$
> f(z) = \frac{1 - (x^{2} + y^{2})}{(1 - x)^{2} + y^{2}} + i \frac{2y}{(1 - x)^{2} + y^{2}},
> $$
> 所以 $f$ 将上半平面中的半圆盘映到第一象限。其逆映射由 $g(w) = \dfrac{w - 1}{w + 1}$ 给出，显然在第一象限全纯。此外，对第一象限中所有 $w$，有 $|w + 1| > |w - 1|$，因为 $w$ 到 $-1$ 的距离大于 $w$ 到 $1$ 的距离；因此 $g$ 映到单位圆盘内。最后，容易计算表明，只要 $w$ 在第一象限，$g(w)$ 的虚部就是正的。所以 $g$ 将第一象限变换为所需的半圆盘，而由于 $g$ 是 $f$ 的逆，我们断定 $f$ 是共形映射。
>
> 为了考察 $f$ 在边界上的作用，注意若 $z = e^{i\theta}$ 属于上半单位圆，则
> $$
> f(z) = \frac{1 + e^{i\theta}}{1 - e^{i\theta}} = \frac{e^{-i\theta/2} + e^{i\theta/2}}{e^{-i\theta/2} - e^{i\theta/2}} = \frac{i}{\tan(\theta/2)}.
> $$
> 当 $\theta$ 从 $0$ 变到 $\pi$ 时，我们看到 $f(e^{i\theta})$ 沿虚轴从无穷远走到 $0$。此外，若 $z = x$ 是实数，则
> $$
> f(z) = \frac{1 + x}{1 - x}
> $$
> 也是实数；由此可知，$f$ 实际上是从 $(-1, 1)$ 到正实轴的双射，且当 $x$ 从 $-1$ 变到 $1$ 时，$f(x)$ 从 $0$ 递增到无穷大。注意还有 $f(0) = 1$。

> [!example] 对数映射 ^ex-log-map
> 映射 $z \mapsto \log z$（定义为去掉负虚轴所得到的对数分支）将上半平面映到带形 $\{w = u + iv : u \in \mathbb{R},\ 0 < v < \pi\}$。这由如下事实直接得出：若 $z = re^{i\theta}$ 满足 $-\pi/2 < \theta < 3\pi/2$，则按定义
> $$
> \log z = \log r + i\theta.
> $$
> 其逆映射为 $w \mapsto e^{w}$。
>
> 当 $x$ 从 $-\infty$ 变到 $0$ 时，点 $f(x)$ 在直线 $\{x + i\pi : -\infty < x < \infty\}$ 上从 $\infty + i\pi$ 变到 $-\infty + i\pi$。当 $x$ 在实轴上从 $0$ 变到 $\infty$ 时，其像 $f(x)$ 则沿实轴从 $-\infty$ 变到 $\infty$。

> [!example] 半圆盘到半带形 ^ex-half-disc-to-half-strip
> 根据 [[#^ex-log-map|示例 4]]，我们看到 $z \mapsto \log z$ 也将半圆盘 $\{z = x + iy : |z| < 1,\ y > 0\}$ 共形地映到半带形 $\{w = u + iv : u < 0,\ 0 < v < \pi\}$。当 $x$ 在实轴上从 $0$ 变到 $1$ 时，$\log x$ 从 $-\infty$ 变到 $0$。当 $x$ 在上半平面的单位圆上从 $1$ 变到 $-1$ 时，点 $\log x$ 从 $0$ 变到 $\pi i$（沿带形的垂直段）。最后，当 $x$ 从 $-1$ 变到 $0$ 时，点 $\log x$ 从 $\pi i$ 变到 $-\infty + i\pi$（沿带形的上半直线）。

> [!example] 半带形到半圆盘 ^ex-half-strip-to-half-disc
> 映射 $f(z) = e^{iz}$ 将半带形 $\{z = x + iy : -\pi/2 < x < \pi/2,\ y > 0\}$ 共形地映到半圆盘 $\{w = u + iv : |w| < 1,\ u > 0\}$。这由如下事实直接得出：若 $z = x + iy$，则
> $$
> e^{iz} = e^{-y} e^{ix}.
> $$
> 若 $x$ 从 $\pi/2 + i\infty$ 变到 $\pi/2$，则 $f(x)$ 从 $0$ 变到 $i$；当 $x$ 从 $\pi/2$ 变到 $-\pi/2$ 时，$f(x)$ 在半圆上从 $i$ 变到 $-i$；最后，当 $x$ 从 $-\pi/2$ 变到 $-\pi/2 + i\infty$ 时，$f(x)$ 从 $-i$ 回到 $0$。
>
> 该映射 $f$ 与 [[#^ex-half-disc-to-half-strip|示例 5]] 中的映射密切相关（实际上是其逆）。

> [!example] 儒科夫斯基映射 ^ex-joukowsky
> 函数 $f(z) = -\frac{1}{2} (z + 1 / z)$ 将半圆盘 $\{z = x + iy : |z| < 1,\ y > 0\}$ 共形地映到上半平面（习题 5）。
>
> $f$ 的边界行为如下：若 $x$ 从 $0$ 变到 $1$，则 $f(x)$ 在实轴上从 $\infty$ 变到 $1$。若 $z = e^{i\theta}$，则 $f(z) = \cos \theta$；当 $x$ 在上半平面的单位半圆上从 $1$ 变到 $-1$ 时，$f(x)$ 在实线段上从 $1$ 变到 $-1$。最后，当 $x$ 从 $-1$ 变到 $0$ 时，$f(x)$ 沿实轴从 $-1$ 变到 $-\infty$。

> [!example] 正弦映射 ^ex-sine-map
> 映射 $f(z) = \sin z$ 将上半平面共形地映到半带形 $\{w = x + iy : -\pi/2 < x < \pi/2,\ y > 0\}$。为了看清这一点，注意若 $\zeta = e^{iz}$，则
> $$
> \sin z = \frac{e^{iz} - e^{-iz}}{2i} = -\frac{1}{2} \left(i \zeta + \frac{1}{i \zeta}\right),
> $$
> 因此 $f$ 可通过先应用 [[#^ex-half-strip-to-half-disc|示例 6]] 中的映射，再乘以 $i$（即旋转 $\pi/2$），最后应用 [[#^ex-joukowsky|示例 7]] 中的映射而得到。
>
> 当 $x$ 从 $-\pi/2 + i\infty$ 变到 $-\pi/2$ 时，点 $f(x)$ 从 $-\infty$ 变到 $-1$。当 $x$ 是实数且介于 $-\pi/2$ 与 $\pi/2$ 之间时，$f(x)$ 也是实数且介于 $-1$ 与 $1$ 之间。最后，若 $x$ 从 $\pi/2$ 变到 $\pi/2 + i\infty$，则 $f(x)$ 在实轴上从 $1$ 变到 $\infty$。

## 带形区域上的 Dirichlet 问题 ^dirichlet-strip

开集 $\Omega$ 上的 Dirichlet 问题是指求解
$$
\begin{cases}
\Delta u = 0, & \Omega , \\
u = f, & \partial \Omega ,
\end{cases}  \tag{1}
$$
其中 $\Delta$ 表示拉普拉斯算子 $\dfrac{\partial^2}{\partial x^2} + \dfrac{\partial^2}{\partial y^2}$，而 $f$ 是 $\Omega$ 边界上的给定函数。换言之，我们希望找到一个在 $\Omega$ 内调和且具有给定边界值 $f$ 的函数。在 $\Omega$ 为单位圆盘或上半平面的情形下，本书第一册已经讨论过这个问题，它出现在稳态热传导方程的解中。在这些具体例子中，通过泊松核的卷积得到了显式解。

我们在此的目标是将 Dirichlet 问题与迄今为止讨论的共形映射联系起来。我们首先给出当 $\Omega$ 为带形区域时问题 (1) 的解的公式。事实上，这个例子在第一册第 5 章问题 3 中已经研究过，当时使用 Fourier 变换求解。在此，我们仅使用共形映射和圆盘上的已知解来重新得到这个解。

我们使用的第一个重要事实是：调和函数与全纯函数的复合仍然是调和的。

> [!lemma] 调和函数与全纯函数的复合 ^lem-harmonic-composition
> 设 $V$ 和 $U$ 是 $\mathbb{C}$ 中的开集，$F: V \to U$ 是全纯函数。若 $u: U \to \mathbb{C}$ 是调和函数，则 $u \circ F$ 在 $V$ 上调和。

> [!proof]-
> 该引理的本质是局部的，因此我们可以假设 $U$ 是一个开圆盘。设 $G$ 是 $U$ 上的全纯函数，其实部为 $u$（由第 2 章习题 12，这样的 $G$ 存在，且相差一个加性常数）。令 $H = G \circ F$，并注意到 $u \circ F$ 是 $H$ 的实部。由于 $H$ 全纯，故 $u \circ F$ 调和。
>
> 该引理的另一种（计算性）证明见习题 6。

有了这个结果，我们现在可以考虑当 $\Omega$ 为水平带形
$$
\Omega = \{x + iy : x \in \mathbb{R},\ 0 < y < 1\} \tag{2}
$$
时的问题 (1)，其边界是两条水平直线 $\mathbb{R}$ 和 $i + \mathbb{R}$ 的并集。我们将边界数据表示为定义在 $\mathbb{R}$ 上的两个函数 $f_0$ 和 $f_1$，并寻求 $\Omega$ 中满足 $\Delta u = 0$ 的解 $u(x,y)$，使得
$$
u(x, 0) = f_0(x), \quad u(x, 1) = f_1(x). \tag{3}
$$
我们假设 $f_0$ 和 $f_1$ 连续且在无穷远处消失，即 $\displaystyle \lim_{|x| \to \infty} f_j(x) = 0$（$j = 0, 1$）。

我们将采用的方法是通过共形映射将问题从带形区域转移到单位圆盘。在圆盘上，解 $\tilde{u}$ 用泊松核的卷积表示。最后，使用之前共形映射的逆将 $\tilde{u}$ 移回带形区域，从而给出问题的最终答案。

为了实现我们的目标，我们引入映射 $F: \mathbb{D} \to \Omega$ 和 $G: \Omega \to \mathbb{D}$，定义如下：
$$
F(w) = \frac{1}{\pi} \log \left(i \frac{1 - w}{1 + w}\right), \quad  G(z) = \frac{i - e^{\pi z}}{i + e^{\pi z}}. \tag{4}
$$
这两个函数由 [[#^ex-power-function|幂函数]]、[[#^ex-log-map|对数映射]] 等示例中的映射复合得到，它们互为逆映射且都是共形映射。通过追踪 $F$ 的边界行为，我们发现它将下半圆映为直线 $i + \mathbb{R}$，将上半圆映为 $\mathbb{R}$。更精确地说，当 $\varphi$ 从 $-\pi$ 变到 $0$ 时，$F(e^{i\varphi})$ 从 $i + \infty$ 变到 $i - \infty$；当 $\varphi$ 从 $0$ 变到 $\pi$ 时，$F(e^{i\varphi})$ 在实轴上从 $-\infty$ 变到 $\infty$。

考虑到 $F$ 在圆周上的行为，我们定义
$$
\tilde{f}_1(\varphi) = f_1(F(e^{i\varphi}) - i), \quad  -\pi < \varphi < 0, \tag{5}
$$
和
$$
\tilde{f}_0(\varphi) = f_0(F(e^{i\varphi})), \quad 0 < \varphi < \pi. \tag{6}
$$
由于 $f_0$ 和 $f_1$ 在无穷远处消失，函数 $\tilde{f}$（在下半圆等于 $\tilde{f}_1$，在上半圆等于 $\tilde{f}_0$，且在 $\varphi = \pm \pi, 0$ 处为零）在整个圆周上连续。单位圆盘上以 $\tilde{f}$ 为边界数据的 Dirichlet 问题的解由泊松积分给出：
$$
\tilde{u}(w) = \frac{1}{2\pi} \int_{-\pi}^{\pi} P_r(\theta - \varphi) \tilde{f}(\varphi) \, d\varphi
= \frac{1}{2\pi} \int_{-\pi}^{0} P_r(\theta - \varphi) \tilde{f}_1(\varphi) \, d\varphi + \frac{1}{2\pi} \int_{0}^{\pi} P_r(\theta - \varphi) \tilde{f}_0(\varphi) \, d\varphi, \tag{7}
$$
其中 $w = re^{i\theta}$，而
$$
P_r(\theta) = \frac{1 - r^2}{1 - 2r \cos \theta + r^2} \tag{8}
$$
是泊松核。[[#^lem-harmonic-composition|引理 1]] 保证了由
$$
u(z) = \tilde{u}(G(z)) \tag{9}
$$
定义的函数 $u$ 在带形区域中调和。此外，我们的构造也确保了 $u$ 具有正确的边界值。

首先在点 $z = iy$（$0 < y < 1$）处得到用 $f_0$ 和 $f_1$ 表示 $u$ 的公式。适当的变量替换（见习题 7）表明，若 $re^{i\theta} = G(iy)$，则
$$
\frac{1}{2\pi} \int_{0}^{\pi} P_r(\theta - \varphi) \tilde{f}_0(\varphi) \, d\varphi = \frac{\sin \pi y}{2} \int_{-\infty}^{\infty} \frac{f_0(t)}{\cosh \pi t - \cos \pi y} \, dt. \tag{10}
$$
类似的计算也给出
$$
\frac{1}{2\pi} \int_{-\pi}^{0} P_r(\theta - \varphi) \tilde{f}_1(\varphi) \, d\varphi = \frac{\sin \pi y}{2} \int_{-\infty}^{\infty} \frac{f_1(t)}{\cosh \pi t + \cos \pi y} \, dt. \tag{11}
$$
将 (10) 和 (11) 相加，得到 $u(0, y)$ 的公式。一般地，回忆第一册第 5 章习题 13，在无穷远处消失的带形区域上 Dirichlet 问题的解是唯一的。因此，边界条件的平移 $x$ 也会导致解平移 $x$。将同样的论证应用于 $f_0(x + t)$ 和 $f_1(x + t)$（$x$ 固定），再进行一次变量替换，可得
$$
u(x, y) = \frac{\sin \pi y}{2} \left( \int_{-\infty}^{\infty} \frac{f_0(x - t)}{\cosh \pi t - \cos \pi y} \, dt + \int_{-\infty}^{\infty} \frac{f_1(x - t)}{\cosh \pi t + \cos \pi y} \, dt \right), \tag{12}
$$
这就给出了带形区域上 Dirichlet 问题的一个解。特别地，我们发现解是用函数 $f_0$ 和 $f_1$ 的卷积给出的。另外，注意在带形区域的中点（$y = 1/2$），解是通过函数 $1/\cosh \pi t$ 的积分给出的；正如我们在第 3 章例 3 中所见，这个函数恰好是其自身的 Fourier 变换。


# 2. Schwarz 引理；圆盘与上半平面的自同构 ^schwarz-lemma-automorphisms

Schwarz 引理的叙述和证明都很简单，但该结果的应用却十分深远。我们回顾一下，旋转是形如 $z \mapsto cz$ 且 $|c| = 1$ 的映射，即 $c = e^{i\theta}$，其中 $\theta \in \mathbb{R}$ 称为旋转角，在相差 $2\pi$ 的整数倍的意义下是唯一确定的。

> [!lemma] Schwarz 引理 ^lem-schwarz
> 设 $f: \mathbb{D} \to \mathbb{D}$ 是全纯函数且 $f(0) = 0$。则
> 1. 对所有 $z \in \mathbb{D}$，有 $|f(z)| \leq |z|$。
> 2. 若存在某个 $z_0 \neq 0$ 使得 $|f(z_0)| = |z_0|$，则 $f$ 是一个旋转。
> 3. $|f'(0)| \leq 1$，且若等号成立，则 $f$ 是一个旋转。

> [!proof]-
> 我们首先将 $f$ 在 $0$ 处展开为幂级数，该级数在整个 $\mathbb{D}$ 上收敛：
> $$
> f(z) = a_0 + a_1 z + a_2 z^2 + \cdots.
> $$
> 由于 $f(0) = 0$，我们有 $a_0 = 0$，因此 $f(z)/z$ 在 $\mathbb{D}$ 上全纯（因为它在 $0$ 处具有可去奇点）。若 $|z| = r < 1$，则由 $|f(z)| \leq 1$ 可得
> $$
> \left| \frac{f(z)}{z} \right| \leq \frac{1}{r},
> $$
> 由最大模原理，只要 $|z| \leq r$ 该不等式就成立。令 $r \to 1$ 即得第一个结论。
>
> 对于 (ii)，我们看到 $f(z)/z$ 在 $\mathbb{D}$ 内部达到最大值，因此必为常数，设为 $f(z) = cz$。在 $z_0$ 处取值并取绝对值，我们发现 $|c| = 1$。因此存在 $\theta \in \mathbb{R}$ 使得 $c = e^{i\theta}$，这说明 $f$ 是一个旋转。
>
> 最后，注意到若 $g(z) = f(z)/z$，则在整个 $\mathbb{D}$ 上有 $|g(z)| \leq 1$，并且
> $$
> g(0) = \lim_{z \to 0} \frac{f(z) - f(0)}{z} = f'(0).
> $$
> 因此，若 $|f'(0)| = 1$，则 $|g(0)| = 1$，由最大模原理 $g$ 为常数，这意味着 $f(z) = cz$ 且 $|c| = 1$。

我们对该引理的第一个应用是确定圆盘的自同构。

## 圆盘的自同构 ^automorphisms-disc

从开集 $\Omega$ 到自身的共形映射称为 $\Omega$ 的**自同构**。$\Omega$ 的所有自同构的集合记为 $\operatorname{Aut}(\Omega)$，它构成一个群。群运算是映射的复合，单位元是映射 $z \mapsto z$，逆元就是反函数。显然，若 $f$ 和 $g$ 是 $\Omega$ 的自同构，则 $f \circ g$ 也是自同构，事实上其逆由下式给出：
$$
(f \circ g)^{-1} = g^{-1} \circ f^{-1}.
$$
如上所述，恒等映射总是一个自同构。我们可以给出单位圆盘的其他更有趣的自同构。显然，任意角度 $\theta \in \mathbb{R}$ 的旋转，即 $r_{\theta}: z \mapsto e^{i\theta}z$，是单位圆盘的自同构，其逆是角度为 $-\theta$ 的旋转，即 $r_{-\theta}: z \mapsto e^{-i\theta}z$。更有趣的是如下形式的自同构：
$$
\psi_{\alpha}(z) = \frac{\alpha - z}{1 - \overline{\alpha}z}, \quad \text{其中 } \alpha \in \mathbb{C} \text{ 且 } |\alpha| < 1, \tag{1}
$$
这些映射在第 1 章习题 7 中引入，由于它们有许多有用的性质，在复分析的许多问题中都有出现。证明它们是 $\mathbb{D}$ 的自同构相当简单。首先，由于 $|\alpha| < 1$，映射 $\psi_{\alpha}$ 在单位圆盘上全纯。若 $|z| = 1$，则 $z = e^{i\theta}$ 且
$$
\psi_{\alpha}(e^{i\theta}) = \frac{\alpha - e^{i\theta}}{e^{i\theta}(e^{-i\theta} - \overline{\alpha})} = e^{-i\theta} \frac{w}{\overline{w}},
$$
其中 $w = \alpha - e^{i\theta}$，因此 $|\psi_{\alpha}(z)| = 1$。由最大模原理，我们断定对所有 $z \in \mathbb{D}$ 有 $|\psi_{\alpha}(z)| < 1$。最后我们观察到以下简单事实：
$$
\begin{aligned}
\left(\psi_{\alpha} \circ \psi_{\alpha}\right)(z) &= \frac{\alpha - \frac{\alpha - z}{1 - \overline{\alpha} z}}{1 - \overline{\alpha} \frac{\alpha - z}{1 - \overline{\alpha} z}} \\
&= \frac{\alpha - |\alpha|^2 z - \alpha + z}{1 - \overline{\alpha} z - |\alpha|^2 + \overline{\alpha} z} \\
&= \frac{(1 - |\alpha|^2) z}{1 - |\alpha|^2} \\
&= z,
\end{aligned}
$$
由此我们得出结论：$\psi_{\alpha}$ 是自身的逆！$\psi_{\alpha}$ 的另一个重要性质是它在 $z = \alpha$ 处为零；此外它交换 $0$ 和 $\alpha$，即
$$
\psi_{\alpha}(0) = \alpha \quad \& \quad \psi_{\alpha}(\alpha) = 0.
$$

下面的定理说明，旋转与映射 $\psi_{\alpha}$ 的组合穷尽了圆盘的所有自同构。

> [!theorem] 圆盘的自同构 ^thm-automorphisms-disc
> 若 $f$ 是圆盘的一个自同构，则存在 $\theta \in \mathbb{R}$ 和 $\alpha \in \mathbb{D}$ 使得
> $$
> f(z) = e^{i\theta} \frac{\alpha - z}{1 - \overline{\alpha} z}. \tag{2}
> $$

> [!proof]-
> 由于 $f$ 是圆盘的自同构，存在唯一的复数 $\alpha \in \mathbb{D}$ 使得 $f(\alpha) = 0$。现在我们考虑由 $g = f \circ \psi_{\alpha}$ 定义的自同构 $g$。则 $g(0) = 0$，[[#^lem-schwarz|Schwarz 引理]] 给出
> $$
> |g(z)| \leq |z|, \quad \forall z \in \mathbb{D}. \tag{3}
> $$
> 此外，$g^{-1}(0) = 0$，因此对 $g^{-1}$ 应用 [[#^lem-schwarz|Schwarz 引理]]，我们发现
> $$
> |g^{-1}(w)| \leq |w|, \quad \forall w \in \mathbb{D}.
> $$
> 将最后一个不等式用于每个 $z \in \mathbb{D}$ 的 $w = g(z)$，得到
> $$
> |z| \leq |g(z)|, \quad \forall z \in \mathbb{D}. \tag{4}
> $$
> 结合 (3) 和 (4) 我们发现对所有 $z \in \mathbb{D}$ 有 $|g(z)| = |z|$，由 [[#^lem-schwarz|Schwarz 引理]] 我们断定 $g(z) = e^{i\theta}z$ 对某个 $\theta \in \mathbb{R}$ 成立。将 $z$ 替换为 $\psi_{\alpha}(z)$ 并利用 $(\psi_{\alpha} \circ \psi_{\alpha})(z) = z$，我们推得 $f(z) = e^{i\theta}\psi_{\alpha}(z)$，如所证。

在定理中令 $\alpha = 0$ 得到以下推论。

> [!corollary] ^cor-rotations-only
> 固定原点的单位圆盘的唯一自同构是旋转。

注意，通过使用映射 $\psi_{\alpha}$，我们可以看到圆盘自同构群的作用是可迁的，即对于圆盘中的任意一对点 $\alpha$ 和 $\beta$，存在自同构 $\psi$ 将 $\alpha$ 映为 $\beta$。这样的 $\psi$ 由 $\psi = \psi_{\beta} \circ \psi_{\alpha}$ 给出。

$\mathbb{D}$ 的自同构的显式公式给出了群 $\operatorname{Aut}(\mathbb{D})$ 的一个很好的描述。事实上，这个自同构群“几乎”同构于一个通常记为 $\mathrm{SU}(1,1)$ 的复系数 $2 \times 2$ 矩阵群。该群由所有保持 $\mathbb{C}^{2} \times \mathbb{C}^{2}$ 上埃尔米特型
$$
\langle Z, W \rangle = z_{1}\overline{w}_{1} - z_{2}\overline{w}_{2},
$$
（其中 $Z = (z_{1}, z_{2})$，$W = (w_{1}, w_{2})$）的 $2 \times 2$ 矩阵组成。关于这个主题的更多信息，我们请读者参考问题 4。

## 上半平面的自同构 ^automorphisms-halfplane

我们对 $\mathbb{D}$ 的自同构的了解，连同 [[#^dirichlet-strip|第 1.1 节]] 中发现的共形映射 $F: \mathbb{H} \to \mathbb{D}$，使我们能够确定 $\mathbb{H}$ 的自同构群，记作 $\operatorname{Aut}(\mathbb{H})$。

考虑映射
$$
\Gamma: \operatorname{Aut}(\mathbb{D}) \to \operatorname{Aut}(\mathbb{H})
$$
由“用 $F$ 共轭”给出：
$$
\Gamma(\varphi) = F^{-1} \circ \varphi \circ F.
$$
显然，当 $\varphi$ 是 $\mathbb{D}$ 的自同构时，$\Gamma(\varphi)$ 是 $\mathbb{H}$ 的自同构，且 $\Gamma$ 是双射，其逆由 $\Gamma^{-1}(\psi) = F \circ \psi \circ F^{-1}$ 给出。事实上，我们还能证明更多，即 $\Gamma$ 保持相应自同构群上的运算。实际上，假设 $\varphi_{1}, \varphi_{2} \in \operatorname{Aut}(\mathbb{D})$。由于 $F \circ F^{-1}$ 是 $\mathbb{D}$ 上的恒等映射，我们发现
$$
\Gamma(\varphi_{1} \circ \varphi_{2}) = F^{-1} \circ \varphi_{1} \circ \varphi_{2} \circ F = F^{-1} \circ \varphi_{1} \circ F \circ F^{-1} \circ \varphi_{2} \circ F = \Gamma(\varphi_{1}) \circ \Gamma(\varphi_{2}).
$$
结论是两个群 $\operatorname{Aut}(\mathbb{D})$ 和 $\operatorname{Aut}(\mathbb{H})$ 是相同的，因为 $\Gamma$ 定义了它们之间的一个同构。我们仍需给出 $\operatorname{Aut}(\mathbb{H})$ 中元素的描述。通过 $F$ 将圆盘的自同构拉回到上半平面的一系列计算可用于验证 $\operatorname{Aut}(\mathbb{H})$ 由所有如下形式的映射组成：
$$
z \mapsto \frac{az + b}{cz + d}, \tag{5}
$$
其中 $a, b, c, d$ 是实数且 $ad - bc = 1$。同样，背后隐藏着一个矩阵群。令 $\mathrm{SL}_2(\mathbb{R})$ 表示所有实系数且行列式为 1 的 $2 \times 2$ 矩阵构成的群，即
$$
\mathrm{SL}_2(\mathbb{R}) = \left\{ M = \begin{pmatrix} a & b \\ c & d \end{pmatrix} : a, b, c, d \in \mathbb{R},\  \&\  \det(M) = ad - bc = 1 \right\}. \tag{6}
$$
这个群称为**特殊线性群**。

给定一个矩阵 $M \in \mathrm{SL}_2(\mathbb{R})$，我们定义映射 $f_{M}$ 为
$$
f_{M}(z) = \frac{az + b}{cz + d}. \tag{7}
$$

> [!theorem] 上半平面的自同构 ^thm-automorphisms-halfplane
> $\mathbb{H}$ 的每个自同构都具有 $f_{M}$ 的形式，其中 $M \in \mathrm{SL}_2(\mathbb{R})$。反之，每个这种形式的映射都是 $\mathbb{H}$ 的自同构。

**证明**由一系列步骤组成。为简洁起见，我们将群 $\mathrm{SL}_2(\mathbb{R})$ 记为 $\mathcal{G}$。

1. **若 $M \in \mathcal{G}$，则 $f_{M}$ 将 $\mathbb{H}$ 映到自身。** 这由以下观察显然：
   $$
   \operatorname{Im}(f_{M}(z)) = \frac{(ad - bc) \operatorname{Im}(z)}{|cz + d|^2} = \frac{\operatorname{Im}(z)}{|cz + d|^2} > 0 \quad \text{只要 } z \in \mathbb{H}. \tag{8}
   $$

2. **若 $M$ 和 $M'$ 是 $\mathcal{G}$ 中的两个矩阵，则 $f_{M} \circ f_{M'} = f_{MM'}$。** 这由直接计算得到，此处略去。作为推论，我们可以证明定理的前半部分。每个 $f_{M}$ 是自同构，因为它有一个全纯逆 $(f_{M})^{-1}$，即 $f_{M^{-1}}$。事实上，若 $I$ 是单位矩阵，则
   $$
   (f_{M} \circ f_{M^{-1}})(z) = f_{MM^{-1}}(z) = f_{I}(z) = z.
   $$

3. **给定 $\mathbb{H}$ 中的任意两点 $z$ 和 $w$，存在 $M \in \mathcal{G}$ 使得 $f_{M}(z) = w$，因此 $\mathcal{G}$ 在 $\mathbb{H}$ 上的作用是可迁的。** 要证明这一点，只需证明我们可以将任意 $z \in \mathbb{H}$ 映为 $i$。在 (8) 中令 $d = 0$ 得
   $$
   \operatorname{Im}(f_{M}(z)) = \frac{\operatorname{Im}(z)}{|cz|^2}
   $$
   我们可以选取实数 $c$ 使得 $\operatorname{Im}(f_{M}(z)) = 1$。然后选取矩阵
   $$
   M_1 = \begin{pmatrix} 0 & -c^{-1} \\ c & 0 \end{pmatrix}
   $$
   使得 $f_{M_1}(z)$ 的虚部等于 1。然后我们用如下形式的矩阵进行平移：
   $$
   M_2 = \begin{pmatrix} 1 & b \\ 0 & 1 \end{pmatrix}, \quad  b \in \mathbb{R},
   $$
   将 $f_{M_1}(z)$ 变为 $i$。最后，映射 $f_{M}$ 其中 $M = M_2M_1$ 将 $z$ 映为 $i$。

4. **若 $\theta$ 是实数，则矩阵**
   $$
   M_\theta = \begin{pmatrix} \cos \theta & -\sin \theta \\ \sin \theta & \cos \theta \end{pmatrix} \tag{9}
   $$
   属于 $\mathcal{G}$，并且若 $F: \mathbb{H} \to \mathbb{D}$ 表示标准的共形映射，则 $F \circ f_{M_\theta} \circ F^{-1}$ 对应于圆盘中的角度为 $-2\theta$ 的旋转。这由以下事实得到：$F \circ f_{M_\theta} = e^{-2i\theta} F(z)$，这很容易验证。

5. **我们现在可以完成定理的证明。** 假设 $f$ 是 $\mathbb{H}$ 的自同构且满足 $f(\beta) = i$，并考虑矩阵 $N \in \mathcal{G}$ 使得 $f_{N}(i) = \beta$。则 $g = f \circ f_{N}$ 满足 $g(i) = i$，因此 $F \circ g \circ F^{-1}$ 是固定原点的圆盘自同构。由 [[#^cor-rotations-only|推论 1]]，$F \circ g \circ F^{-1}$ 是一个旋转，再由第 4 步知存在 $\theta \in \mathbb{R}$ 使得
   $$
   F \circ g \circ F^{-1} = F \circ f_{M_\theta} \circ F^{-1}.
   $$
   因此 $g = f_{M_\theta}$，我们得出结论 $f = f_{M_\theta N^{-1}}$，这正是所需的形式。

最后一个观察是，群 $\operatorname{Aut}(\mathbb{H})$ 并不完全同构于 $\mathrm{SL}_2(\mathbb{R})$。原因是两个矩阵 $M$ 和 $-M$ 给出相同的函数 $f_{M} = f_{-M}$。因此，若我们将两个矩阵 $M$ 和 $-M$ 等同起来，就得到一个新群 $\mathrm{PSL}_2(\mathbb{R})$，称为**射影特殊线性群**；这个群同构于 $\operatorname{Aut}(\mathbb{H})$。

# 3. Riemann 映射定理 ^riemann-mapping

## 必要条件与定理陈述 ^riemann-conditions

现在我们来到本章所承诺的基石。基本问题是确定开集 $\Omega$ 上保证存在共形映射 $F: \Omega \to \mathbb{D}$ 的条件。

一系列简单的观察使我们能够找到 $\Omega$ 的必要条件。首先，若 $\Omega = \mathbb{C}$，则不存在共形映射 $F: \Omega \to \mathbb{D}$，因为由 Liouville 定理 $F$ 必为常数。因此，一个必要条件是假设 $\Omega \neq \mathbb{C}$。由于 $\mathbb{D}$ 是连通的，我们也必须要求 $\Omega$ 是连通的。还有一个条件是被迫施加的：由于 $\mathbb{D}$ 是单连通的，$\Omega$ 也必须是单连通的（见习题 3）。值得注意的是，$\Omega$ 上的这些条件也是保证存在从 $\Omega$ 到 $\mathbb{D}$ 的双全纯映射的充分条件。

为简洁起见，若 $\Omega \subset \mathbb{C}$ 非空且不是整个 $\mathbb{C}$，我们称 $\Omega$ 为**真子集**。

> [!theorem] Riemann 映射定理 ^thm-riemann-mapping
> 假设 $\Omega$ 是真子集且是单连通的。若 $z_0 \in \Omega$，则存在唯一的共形映射 $F: \Omega \to \mathbb{D}$ 使得
> $$
> F(z_0) = 0 \quad \& \quad F'(z_0) > 0. \tag{1}
> $$

> [!corollary] ^cor-conformally-equivalent
> $\mathbb{C}$ 中任意两个真的单连通开子集是共形等价的。

显然，推论可由定理得到，因为我们可以将单位圆盘作为中间步骤。此外，定理中的唯一性断言是直接的，因为若 $F$ 和 $G$ 是从 $\Omega$ 到 $\mathbb{D}$ 且满足这两个条件的共形映射，则 $H = F \circ G^{-1}$ 是固定原点的圆盘自同构。因此 $H(z) = e^{i\theta}z$，由于 $H'(0) > 0$，必有 $e^{i\theta} = 1$，由此我们断定 $F = G$。

本节剩余部分致力于证明共形映射 $F$ 的存在性。证明的思想如下。我们考虑所有满足 $f(z_0) = 0$ 的单叶全纯映射 $f: \Omega \to \mathbb{D}$。从中我们希望选取一个 $f$ 使其像填满整个 $\mathbb{D}$，这可以通过使 $f'(z_0)$ 尽可能大来实现。在这样做时，我们需要能够从给定的函数序列中提取 $f$ 作为极限。我们首先讨论这一点。

## Montel 定理 ^montel

设 $\Omega$ 是 $\mathbb{C}$ 中的开集。一族 $\Omega$ 上的全纯函数 $\mathcal{F}$ 称为**正规族**，如果 $\mathcal{F}$ 中的每个序列都有子序列在 $\Omega$ 的每个紧子集上一致收敛（极限不必属于 $\mathcal{F}$）。

在实践中，证明一个函数族是正规族是两个相关性质——一致有界性和等度连续性——的结果。我们现在定义这些概念。

函数族 $\mathcal{F}$ 称为在 $\Omega$ 的**紧子集上一致有界**，如果对每个紧集 $K \subset \Omega$，存在 $B > 0$ 使得
$$
|f(z)| \leq B, \quad \forall z \in K, f \in \mathcal{F}. \tag{2}
$$

此外，函数族 $\mathcal{F}$ 称为在紧集 $K$ 上**等度连续**，如果对每个 $\epsilon > 0$ 存在 $\delta > 0$ 使得只要 $z, w \in K$ 且 $|z - w| < \delta$，就有
$$
|f(z) - f(w)| < \epsilon, \quad \forall f \in \mathcal{F}. \tag{3}
$$

等度连续性是一个很强的条件，它要求在整个族上一致地具有一致连续性。例如，$[0,1]$ 上任何导数一致有界的可微函数族是等度连续的。这直接由中值定理得到。另一方面，注意 $[0,1]$ 上由 $f_n(x) = x^n$ 给出的族 $\{f_n\}$ 不是等度连续的，因为对任意固定的 $0 < x_0 < 1$，当 $n \to \infty$ 时 $|f_n(1) - f_n(x_0)| \to 1$。

下面的定理将这些新概念结合在一起，是证明 Riemann 映射定理的重要工具。

> [!theorem] Montel 定理 ^thm-montel
> 假设 $\mathcal{F}$ 是 $\Omega$ 上的一族全纯函数，在 $\Omega$ 的紧子集上一致有界。则：
> 1. $\mathcal{F}$ 在 $\Omega$ 的每个紧子集上是等度连续的。
> 2. $\mathcal{F}$ 是正规族。

该定理实际上由两个独立部分组成。第一部分说明，在 $\mathcal{F}$ 是 $\Omega$ 上的一族全纯函数且在紧子集上一致有界的假设下，$\mathcal{F}$ 是等度连续的。证明由 Cauchy 积分公式的应用得到，因此依赖于 $\mathcal{F}$ 由全纯函数组成这一事实。这个结论与实情形成鲜明对比，例如由 $(0,1)$ 上的函数 $f_n(x) = \sin(nx)$ 给出的族是一致有界的，但该族不是等度连续的，并且在 $(0,1)$ 的任何紧子区间上没有收敛子序列。

定理的第二部分本质上不是复解析的。事实上，仅假设 $\mathcal{F}$ 在 $\Omega$ 的紧子集上一致有界且等度连续，就可以推出 $\mathcal{F}$ 是正规族。这个结果有时称为 Arzela-Ascoli 定理，其证明主要由一个对角化论证组成。

我们需要证明在 $\Omega$ 的任意紧子集上的收敛性，因此引入以下概念是有用的。序列 $\{K_{\ell}\}_{\ell=1}^{\infty}$ 称为 $\Omega$ 的一个**穷竭**，如果
1. 对所有 $\ell = 1, 2, \ldots$，$K_{\ell}$ 包含在 $K_{\ell+1}$ 的内部。
2. 任意紧集 $K \subset \Omega$ 都包含在某个 $K_{\ell}$ 中。特别地，$\Omega = \bigcup_{\ell=1}^{\infty} K_{\ell}$。

> [!lemma] 穷竭的存在性 ^lem-exhaustion
> 复平面中的任何开集 $\Omega$ 都有一个穷竭。

> [!proof]-
> 若 $\Omega$ 有界，令 $K_{\ell}$ 表示 $\Omega$ 中所有与 $\Omega$ 的边界距离 $\geq 1/\ell$ 的点构成的集合。若 $\Omega$ 无界，令 $K_{\ell}$ 与上述集合相同，但额外要求对所有 $z \in K_{\ell}$ 有 $|z| \leq \ell$。

我们现在可以开始证明 Montel 定理。设 $K$ 是 $\Omega$ 的紧子集，选取 $r > 0$ 足够小，使得对所有 $z \in K$，$D_{3r}(z) \subset \Omega$。只需选取 $r$ 使得 $3r$ 小于从 $K$ 到 $\Omega$ 边界的距离。设 $z, w \in K$ 且 $|z - w| < r$，并令 $\gamma$ 表示圆盘 $D_{2r}(w)$ 的边界圆。则由 Cauchy 积分公式，我们有
$$
f(z) - f(w) = \frac{1}{2\pi i} \int_{\gamma} f(\zeta) \left[ \frac{1}{\zeta - z} - \frac{1}{\zeta - w} \right] d\zeta. \tag{4}
$$
注意
$$
\left| \frac{1}{\zeta - z} - \frac{1}{\zeta - w} \right| = \frac{|z - w|}{|\zeta - z||\zeta - w|} \leq \frac{|z - w|}{r^2}
$$
因为 $\zeta \in \gamma$ 且 $|z - w| < r$。因此
$$
|f(z) - f(w)| \leq \frac{1}{2\pi} \frac{2\pi r}{r^2} B |z - w| = \frac{B}{r} |z - w|, \tag{5}
$$
其中 $B$ 是族 $\mathcal{F}$ 在与 $K$ 距离 $\leq 2r$ 的所有点构成的紧集上的一致界。因此 $|f(z) - f(w)| < C|z - w|$，这个估计对所有满足 $|z - w| < r$ 的 $z, w \in K$ 和所有 $f \in \mathcal{F}$ 成立；于是该族是等度连续的，如所证。

为了证明定理的第二部分，我们如下论证。设 $\{f_n\}_{n=1}^{\infty}$ 是 $\mathcal{F}$ 中的序列，$K$ 是 $\Omega$ 的紧子集。选取在 $\Omega$ 中稠密的点序列 $\{w_j\}_{j=1}^{\infty}$。由于 $\{f_n\}$ 一致有界，存在 $\{f_n\}$ 的子序列 $\{f_{n,1}\} = \{f_{1,1}, f_{2,1}, f_{3,1}, \ldots\}$ 使得 $f_{n,1}(w_1)$ 收敛。

从 $\{f_{n,1}\}$ 中我们可以提取子序列 $\{f_{n,2}\} = \{f_{1,2}, f_{2,2}, f_{3,2}, \ldots\}$ 使得 $f_{n,2}(w_2)$ 收敛。我们可以继续这个过程，从 $\{f_{n,j-1}\}$ 中提取子序列 $\{f_{n,j}\}$ 使得 $f_{n,j}(w_j)$ 收敛。

最后，令 $g_n = f_{n,n}$ 并考虑对角子序列 $\{g_n\}$。由构造，$g_n(w_j)$ 对每个 $j$ 收敛，我们断言等度连续性意味着 $g_n$ 在 $K$ 上一致收敛。给定 $\epsilon > 0$，选取等度连续性定义中的 $\delta$，并注意到存在某个 $J$，使得 $K$ 包含在圆盘 $D_{\delta}(w_1), \ldots, D_{\delta}(w_J)$ 的并集中。选取 $N$ 足够大，使得当 $n, m > N$ 时，对所有 $j = 1, \ldots, J$ 有
$$
|g_m(w_j) - g_n(w_j)| < \epsilon. \tag{6}
$$
于是若 $z \in K$，则对某个 $1 \leq j \leq J$ 有 $z \in D_{\delta}(w_j)$。因此，
$$
\begin{aligned}
|g_n(z) - g_m(z)| &\leq |g_n(z) - g_n(w_j)| + |g_n(w_j) - g_m(w_j)| + |g_m(w_j) - g_m(z)| \\
&< 3\epsilon
\end{aligned} \tag{7}
$$
只要 $n, m > N$。因此 $\{g_n\}$ 在 $K$ 上一致收敛。

最后，我们需要另一个对角化论证来获得在 $\Omega$ 的每个紧子集上一致收敛的子序列。设 $K_1 \subset K_2 \subset \cdots \subset K_{\ell} \subset \cdots$ 是 $\Omega$ 的一个穷竭，并假设 $\{g_{n,1}\}$ 是原始序列 $\{f_n\}$ 的在 $K_1$ 上一致收敛的子序列。从 $\{g_{n,1}\}$ 中提取在 $K_2$ 上一致收敛的子序列 $\{g_{n,2}\}$，依此类推。则 $\{g_{n,n}\}$ 是 $\{f_n\}$ 的在每个 $K_{\ell}$ 上一致收敛的子序列，由于 $K_{\ell}$ 穷竭 $\Omega$，序列 $\{g_{n,n}\}$ 在 $\Omega$ 的任何紧子集上一致收敛，如所证。

在给出 Riemann 映射定理的证明之前，我们还需要一个结果。

> [!proposition] 单叶性的极限保持 ^prop-limit-injective
> 若 $\Omega$ 是 $\mathbb{C}$ 的连通开子集，且 $\{f_n\}$ 是 $\Omega$ 上一列单叶全纯函数，在 $\Omega$ 的每个紧子集上一致收敛到全纯函数 $f$，则 $f$ 要么是单叶的，要么是常数。

> [!proof]-
> 用反证法，假设 $f$ 不是单叶的，则存在 $\Omega$ 中不同的复数 $z_1$ 和 $z_2$ 使得 $f(z_1) = f(z_2)$。定义新序列 $g_n(z) = f_n(z) - f_n(z_1)$，则 $g_n$ 除了 $z_1$ 外没有其他零点，且序列 $\{g_n\}$ 在 $\Omega$ 的紧子集上一致收敛到 $g(z) = f(z) - f(z_1)$。若 $g$ 不恒为零，则 $z_2$ 是 $g$ 的孤立零点（因为 $\Omega$ 是连通的）；因此
> $$
> 1 = \frac{1}{2\pi i} \int_{\gamma} \frac{g'(\zeta)}{g(\zeta)} d\zeta,
> $$
> 其中 $\gamma$ 是以 $z_2$ 为中心的小圆周，选取使得 $g$ 在 $\gamma$ 上及其内部除 $z_2$ 外的任何点都不为零。因此，$1/g_n$ 在 $\gamma$ 上一致收敛到 $1/g$，且由于 $g_n' \to g'$ 在 $\gamma$ 上一致收敛，我们有
> $$
> \frac{1}{2\pi i} \int_{\gamma} \frac{g_n'(\zeta)}{g_n(\zeta)} d\zeta \to \frac{1}{2\pi i} \int_{\gamma} \frac{g'(\zeta)}{g(\zeta)} d\zeta.
> $$
> 但这是一个矛盾，因为 $g_n$ 在 $\gamma$ 内部没有零点，因此
> $$
> \frac{1}{2\pi i} \int_{\gamma} \frac{g_n'(\zeta)}{g_n(\zeta)} d\zeta = 0, \quad \forall n.
> $$

## Riemann 映射定理的证明 ^riemann-proof

一旦我们建立了上述技术性结果，Riemann 映射定理的其余证明就非常简洁。它包含三个步骤，我们分别列出。

### 步骤 1：化归到 $\Omega \subset \mathbb{D}$ 且 $0 \in \Omega$ 的情形

假设 $\Omega$ 是 $\mathbb{C}$ 的一个单连通真开子集。我们断言 $\Omega$ 共形等价于包含原点的单位圆盘的一个开子集。事实上，选取一个不属于 $\Omega$ 的复数 $\alpha$（回忆 $\Omega$ 是真子集），并注意到 $z - \alpha$ 在单连通集 $\Omega$ 上永不为零。因此，我们可以定义一个全纯函数
$$
f(z) = \log(z - \alpha)
$$
具有对数所需的性质。由此得到 $e^{f(z)} = z - \alpha$，这特别证明了 $f$ 是单射。选取一点 $w \in \Omega$，并注意到
$$
f(z) \neq f(w) + 2\pi i, \quad \forall z \in \Omega,
$$
否则，对该关系取指数得到 $z = w$，从而 $f(z) = f(w)$，矛盾。事实上，我们断言 $f(z)$ 严格远离 $f(w) + 2\pi i$，即存在一个以 $f(w) + 2\pi i$ 为中心的圆盘不包含像 $f(\Omega)$ 中的点。否则，存在 $\Omega$ 中的序列 $\{z_n\}$ 使得 $f(z_n) \to f(w) + 2\pi i$。对该关系取指数，由于指数函数连续，必有 $z_n \to w$。但这意味着 $f(z_n) \to f(w)$，矛盾。最后，考虑映射
$$
F(z) = \frac{1}{f(z) - (f(w) + 2\pi i)}.
$$
由于 $f$ 是单射，$F$ 也是单射，因此 $F: \Omega \to F(\Omega)$ 是共形映射。此外，根据我们的分析，$F(\Omega)$ 有界。因此我们可以平移和缩放函数 $F$，以获得从 $\Omega$ 到包含原点的 $\mathbb{D}$ 的开子集的共形映射。

### 步骤 2：极大化 $|f'(0)|$

由第一步，我们可以假设 $\Omega$ 是 $\mathbb{D}$ 的一个开子集且 $0 \in \Omega$。考虑族 $\mathcal{F}$ 由所有满足 $f(0) = 0$ 的从 $\Omega$ 到单位圆盘的单叶全纯函数组成：
$$
\mathcal{F} = \{f: \Omega \to \mathbb{D} \text{ 全纯, 单射且 } f(0) = 0\}.
$$
首先，注意到 $\mathcal{F}$ 非空，因为它包含恒等映射。此外，该族由构造是一致有界的，因为所有函数都被要求映到单位圆盘内。

现在，我们转向寻找最大化 $|f'(0)|$ 的函数 $f \in \mathcal{F}$ 的问题。首先，观察到当 $f$ 在 $\mathcal{F}$ 中变化时，$|f'(0)|$ 一致有界。这由 Cauchy 不等式（第 2 章推论 4.3）应用于以原点为中心的小圆盘得到。

接下来，令
$$
s = \sup_{f \in \mathcal{F}} |f'(0)|,
$$
并选取序列 $\{f_n\} \subset \mathcal{F}$ 使得 $|f_n'(0)| \to s$ 当 $n \to \infty$。由 [[#^thm-montel|Montel 定理]]，该序列有子序列在紧集上一致收敛到 $\Omega$ 上的全纯函数 $f$。由于 $s \geq 1$（因为 $z \mapsto z$ 属于 $\mathcal{F}$），$f$ 非常数，因此由 [[#^prop-limit-injective|命题 1]] 是单射。此外，由连续性有 $|f(z)| \leq 1$ 对所有 $z \in \Omega$ 成立，由最大模原理我们看到 $|f(z)| < 1$。由于显然有 $f(0) = 0$，我们得出结论 $f \in \mathcal{F}$ 且 $|f'(0)| = s$。

### 步骤 3：证明 $f$ 是满射

在最后一步中，我们证明 $f$ 是从 $\Omega$ 到 $\mathbb{D}$ 的共形映射。由于 $f$ 已经是单射，只需证明 $f$ 也是满射。若不然，我们可以构造 $\mathcal{F}$ 中一个函数使其在 $0$ 处的导数大于 $s$。事实上，假设存在 $\alpha \in \mathbb{D}$ 使得 $f(z) \neq \alpha$，并考虑圆盘的自同构 $\psi_{\alpha}$，它交换 $0$ 和 $\alpha$，即
$$
\psi_{\alpha}(z) = \frac{\alpha - z}{1 - \overline{\alpha}z}.
$$
由于 $\Omega$ 是单连通的，$U = (\psi_{\alpha} \circ f)(\Omega)$ 也是单连通的，此外 $U$ 不包含原点。因此可以在 $U$ 上定义平方根函数
$$
g(w) = e^{\frac{1}{2}\log w}.
$$
接下来，考虑函数
$$
F = \psi_{g(\alpha)} \circ g \circ \psi_{\alpha} \circ f.
$$
我们断言 $F \in \mathcal{F}$。显然 $F$ 是全纯的且将 $0$ 映为 $0$。同时 $F$ 映到单位圆盘内，因为复合中的每个函数都具有这一性质。最后，$F$ 是单射。这对于自同构 $\psi_{\alpha}$ 和 $\psi_{g(\alpha)}$ 显然成立；对于平方根 $g$ 和函数 $f$ 也成立，因为后者由假设是单射。若记 $h$ 为平方函数 $h(w) = w^2$，则必有
$$
f = \psi_{\alpha}^{-1} \circ h \circ \psi_{g(\alpha)}^{-1} \circ F = \Phi \circ F.
$$
但 $\Phi$ 将 $\mathbb{D}$ 映到 $\mathbb{D}$ 且 $\Phi(0) = 0$，并且不是单射（因为 $F$ 是单射而 $h$ 不是）。由 [[#^lem-schwarz|Schwarz 引理]] 的最后一部分，我们断定 $|\Phi'(0)| < 1$。一旦我们观察到
$$
f'(0) = \Phi'(0)F'(0),
$$
从而
$$
|f'(0)| < |F'(0)|,
$$
这与 $|f'(0)|$ 在 $\mathcal{F}$ 中的极大性矛盾。

最后，我们将 $f$ 乘以一个绝对值为 $1$ 的复数使得 $f'(0) > 0$，证明结束。

关于此证明的变体，见问题 7。

> [!remark]
> 值得指出的是，在证明中单连通性假设唯一进入的地方是使用对数和平方根。因此，只要（在 $\Omega$ 是真子集的假设之外）假设 $\Omega$ 是**全纯单连通**的，即对 $\Omega$ 中任何全纯函数 $f$ 和任何闭曲线 $\gamma \subset \Omega$，有 $\int_{\gamma} f(z) \, dz = 0$，就足够了。关于这一点的进一步讨论以及单连通性的各种等价性质，见附录 B。
