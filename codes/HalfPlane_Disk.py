import plotly.graph_objects as go
import numpy as np

def HalfPlane_Disk(z, t):
    """参数化的线性分式变换：从恒等映射 (t=0) 过渡到 HalfPlane_Disk 变换 (t=1)"""
    return np.exp(- 1j * np.pi * (1 - t) / 2  ) * ( 1j*t  - z) / (t*z + 1j)

# ========== 1. 生成原始网格（上半平面） ==========
# 水平线：不同虚部 y0 的直线，x 从 -2 到 2
x_vals = np.linspace(-10, 10, 100)          # 每条水平线上的 x 坐标
y_levels = np.linspace(0, 10, 50)       # 水平线的虚部（y0 > 0）

# 垂直线：不同实部 x0 的直线，y 从 0 到 2
y_vals = np.linspace(0, 10, 50)           # 每条垂直线上的 y 坐标
x_levels = np.linspace(-10, 10, 100)        # 垂直线的实部（x0）

# ========== 2. 预计算所有 t 值下的变换结果 ==========
t_values = np.linspace(0, 1, 31)         # 滑块步数（0 到 1 均匀取 31 个值）

# 存储每条水平线在不同 t 下的坐标（每条线由若干点组成）
# 结构：horiz_lines[t_idx][line_idx] = (X_coords, Y_coords)
horiz_lines = []
for t in t_values:
    lines_t = []
    for y0 in y_levels:
        # 该水平线的原始复数点
        z_line = x_vals + 1j * y0
        w = HalfPlane_Disk(z_line, t)             # 变换后的复数点
        lines_t.append((w.real, w.imag))
    horiz_lines.append(lines_t)

# 同理存储垂直线
vert_lines = []
for t in t_values:
    lines_t = []
    for x0 in x_levels:
        z_line = x0 + 1j * y_vals
        w = HalfPlane_Disk(z_line, t)
        lines_t.append((w.real, w.imag))
    vert_lines.append(lines_t)

# ========== 3. 创建 Plotly 图形 ==========
fig = go.Figure()

# 初始状态 (t=0) 的网格：直接显示上半平面的直线网格
for (x_coords, y_coords) in horiz_lines[0]:
    fig.add_trace(go.Scatter(
        x=x_coords, y=y_coords,
        mode='lines',
        line=dict(color='#51A2FF', width=1),
        showlegend=False,
        hoverinfo='none'
    ))
for (x_coords, y_coords) in vert_lines[0]:
    fig.add_trace(go.Scatter(
        x=x_coords, y=y_coords,
        mode='lines',
        line=dict(color='#FF6467', width=1),
        showlegend=False,
        hoverinfo='none'
    ))

# 设置坐标轴范围（固定，以便观察变形）
fig.update_xaxes(range=[-2, 2], title='Re(w)')
fig.update_yaxes(range=[-2, 2], title='Im(w)')
fig.update_layout(
    title='线性分式变换：上半平面 → 单位圆盘',
    width=700,
    height=700,
    plot_bgcolor='white'
)

# ========== 4. 添加滑块 ==========
# 滑块每一步要更新的数据：所有 traces 的 x 和 y
steps = []
for i, t in enumerate(t_values):
    # 构建当前 t 对应的所有水平线和垂直线的坐标
    new_x_h = []
    new_y_h = []
    for (x_coords, y_coords) in horiz_lines[i]:
        new_x_h.append(x_coords)
        new_y_h.append(y_coords)
    new_x_v = []
    new_y_v = []
    for (x_coords, y_coords) in vert_lines[i]:
        new_x_v.append(x_coords)
        new_y_v.append(y_coords)
    
    # 将所有新坐标展平为一个列表（因为 update 的 args 需要依次对应每个 trace）
    # 注意：traces 的顺序是先所有水平线，再所有垂直线
    all_new_x = new_x_h + new_x_v
    all_new_y = new_y_h + new_y_v
    
    step = dict(
        method='update',
        label=f'{t:.2f}',
        args=[{'x': all_new_x, 'y': all_new_y}]   # 更新所有 traces 的 x 和 y
    )
    steps.append(step)

slider = dict(
    active=0,
    steps=steps,
    currentvalue=dict(prefix='参数 t = ', font=dict(size=14)),
    len=0.9,
    x=0.1,
    y=-0.1
)

fig.update_layout(sliders=[slider])

# ========== 5. 保存为 HTML ==========
fig.write_html('HalfPlane_Disk_animation.html', auto_open=False)
