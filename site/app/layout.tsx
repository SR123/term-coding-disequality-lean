import type { Metadata } from 'next';
import './globals.css';

export const metadata: Metadata = {
  icons: { icon: './favicon.svg' },
  title: 'Term coding — paper and formal proof',
  description: 'Søren Riis: One Unit Separates Polynomial Time from Undecidability in Term Coding. An interactive paper and Lean proof companion.',
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
