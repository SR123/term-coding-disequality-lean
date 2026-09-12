import type { NextConfig } from 'next';
const assetPrefix = process.env.PAPER_BASE_PATH || '';
const nextConfig: NextConfig = { output:'export', trailingSlash:true, assetPrefix };
export default nextConfig;
