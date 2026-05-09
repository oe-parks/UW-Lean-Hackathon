// Preset graphs. Each is an object: { name, vertices, edges, positions? }
// `positions` is optional; if absent, Cytoscape will lay out automatically.

export const PRESETS = [
  {
    name: 'Triangle (smallest blossom-trigger)',
    vertices: [0, 1, 2, 3],
    edges: [[0, 1], [1, 2], [2, 0], [2, 3]],
    positions: { 0: [120, 200], 1: [240, 80], 2: [360, 200], 3: [500, 200] },
    note: 'Vertex 3 is the "stem". The triangle 0-1-2 forms an odd cycle that becomes a blossom during BFS.',
  },
  {
    name: 'Path of 5',
    vertices: [0, 1, 2, 3, 4],
    edges: [[0, 1], [1, 2], [2, 3], [3, 4]],
    positions: { 0: [80, 200], 1: [200, 200], 2: [320, 200], 3: [440, 200], 4: [560, 200] },
    note: 'Bipartite warm-up. Maximum matching has 2 edges.',
  },
  {
    name: 'K3,3 (complete bipartite)',
    vertices: [0, 1, 2, 3, 4, 5],
    edges: [[0, 3], [0, 4], [0, 5], [1, 3], [1, 4], [1, 5], [2, 3], [2, 4], [2, 5]],
    positions: { 0: [120, 100], 1: [120, 220], 2: [120, 340], 3: [420, 100], 4: [420, 220], 5: [420, 340] },
    note: 'No blossoms (graph is bipartite). Perfect matching of size 3.',
  },
  {
    name: 'Petersen graph',
    vertices: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    edges: [
      // outer 5-cycle
      [0, 1], [1, 2], [2, 3], [3, 4], [4, 0],
      // inner 5-pointed star
      [5, 7], [7, 9], [9, 6], [6, 8], [8, 5],
      // spokes
      [0, 5], [1, 6], [2, 7], [3, 8], [4, 9],
    ],
    positions: {
      0: [300, 60],  1: [490, 195], 2: [410, 410], 3: [190, 410], 4: [110, 195],
      5: [300, 150], 6: [400, 220], 7: [365, 330], 8: [235, 330], 9: [200, 220],
    },
    note: 'Two 5-cycles joined by a perfect matching. Forces multiple blossoms.',
  },
  {
    name: 'Bow-tie (two triangles share a vertex)',
    vertices: [0, 1, 2, 3, 4],
    edges: [[0, 1], [1, 2], [2, 0], [2, 3], [3, 4], [4, 2]],
    positions: { 0: [80, 100], 1: [80, 300], 2: [280, 200], 3: [480, 100], 4: [480, 300] },
    note: 'Maximum matching size = 2; vertex 2 ends up unmatched.',
  },
  {
    name: 'C5 (odd cycle)',
    vertices: [0, 1, 2, 3, 4],
    edges: [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]],
    positions: { 0: [300, 60], 1: [480, 200], 2: [400, 380], 3: [200, 380], 4: [120, 200] },
    note: 'A pure odd cycle. Maximum matching size = 2; one vertex unmatched.',
  },
];
