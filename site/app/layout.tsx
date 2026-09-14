import type { Metadata } from 'next';
import './globals.css';

const paperUrl = 'https://sr123.github.io/term-coding-disequality-lean/';
const previewTitle = 'Term Coding — Interactive Paper & Lean Proof Explorer';
const previewDescription = 'Explore Søren Riis’s research paper alongside formal statements, Lean proofs and verification evidence, with external assumptions made explicit.';
const previewImage = {
  url: `${paperUrl}og.jpg`,
  width: 1774,
  height: 887,
  alt: 'Term Coding — Interactive Paper & Lean Proof Explorer, by Søren Riis, beside a branching proof diagram.',
};

export const metadata: Metadata = {
  icons: { icon: './favicon.svg' },
  title: 'Term coding — paper and formal proof',
  description: 'Søren Riis: One Unit Separates Polynomial Time from Undecidability in Term Coding. An interactive paper and Lean proof companion.',
  alternates: { canonical: paperUrl },
  openGraph: {
    type: 'website',
    url: paperUrl,
    siteName: 'Term coding: paper and formal proof',
    title: previewTitle,
    description: previewDescription,
    images: [previewImage],
  },
  twitter: {
    card: 'summary_large_image',
    title: previewTitle,
    description: previewDescription,
    images: [{ url: previewImage.url, alt: previewImage.alt }],
  },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body>
        {children}
      </body>
    </html>
  );
}
