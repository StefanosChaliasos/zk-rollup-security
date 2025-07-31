#!/usr/bin/env python3
"""
Script to analyze Alloy verification results and create publication-quality graphs.
"""

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
import glob
import os
from pathlib import Path

def parse_time(time_str):
    """Parse time string like '499ms' or '1057ms' and return seconds."""
    if 'ms' in time_str:
        return float(time_str.replace('ms', '')) / 1000
    elif 's' in time_str:
        return float(time_str.replace('s', ''))
    else:
        return float(time_str)

def extract_step_number(step_str):
    """Extract the maximum step number from strings like '1..1', '1..2', etc."""
    return int(step_str.split('..')[-1])

def load_results_data(results_dir):
    """Load all CSV files from a results directory and aggregate the data."""
    all_data = []
    
    # Get all CSV files in the directory
    csv_files = glob.glob(os.path.join(results_dir, "alloy_results_cmd*.csv"))
    
    for csv_file in csv_files:
        try:
            df = pd.read_csv(csv_file)
            
            # Skip files with only header or incomplete data
            if len(df) <= 1:
                continue
                
            # Parse time column
            df['Time_seconds'] = df['Time'].apply(parse_time)
            
            # Extract step numbers
            df['Step_num'] = df['Step'].apply(extract_step_number)
            
            # Extract scope from the first command
            if len(df) > 0:
                command = df.iloc[0]['Command']
                if 'for 5 but' in command:
                    scope = 5
                elif 'for 10 but' in command:
                    scope = 10
                else:
                    # Try to extract scope from command
                    scope = int(command.split('for ')[1].split(' but')[0])
                df['Scope'] = scope
            
            all_data.append(df)
            
        except Exception as e:
            print(f"Error reading {csv_file}: {e}")
            continue
    
    if not all_data:
        return pd.DataFrame()
    
    # Combine all data
    combined_df = pd.concat(all_data, ignore_index=True)
    return combined_df

def categorize_mechanism(command):
    """Categorize the command into mechanism types."""
    if 'c_srp' in command:
        return 'Simple'
    elif 'c_fqp' in command:
        return 'Forced Queue'
    elif 'c_blacklist_prop_all_censored' in command:
        return 'Blacklist'
    elif 'c_up' in command:
        return 'Upgradeability'
    elif 'c_bp' in command:
        return 'Blacklist'  # Additional blacklist properties
    else:
        return 'Unknown'

def create_comprehensive_mechanism_tables():
    """Create comprehensive tables by mechanism type for different step ranges and statistics."""
    
    # Load data for scope 5
    scope5_data = load_results_data("results/results_5_10")
    
    if scope5_data.empty:
        print("Error: Could not load data from results_5_10 directory")
        return
    
    # Add mechanism categorization
    scope5_data['Mechanism'] = scope5_data['Command'].apply(categorize_mechanism)
    
    # Get only the first property for each mechanism
    first_properties = {
        'Simple': 'c_srp1',
        'Forced Queue': 'c_fqp1', 
        'Blacklist': 'c_bp1',
        'Upgradeability': 'c_up1'
    }
    
    # Filter to only include the first property for each mechanism
    filtered_data = scope5_data[scope5_data['Command'].str.contains('|'.join(first_properties.values()))]
    
    # Add lines of code
    loc_mapping = {
        'Simple': 295,
        'Forced Queue': 529,
        'Blacklist': 721,
        'Upgradeability': 970
    }
    
    # Create tables for different step ranges and statistics
    step_ranges = [5, 10]
    stat_types = ['median', 'sum', 'min', 'max']
    
    for steps in step_ranges:
        # Filter data for current step range
        step_data = filtered_data[filtered_data['Step_num'] <= steps]
        
        for stat_type in stat_types:
            if stat_type == 'sum':
                # For sum, we need to group by mechanism and sum across all steps
                stats = step_data.groupby('Mechanism').agg({
                    'Clauses': 'sum',
                    'Time_seconds': 'sum'
                }).reset_index()
            else:
                # For median, min, max, we calculate the statistic across all measurements
                stats = step_data.groupby('Mechanism').agg({
                    'Clauses': stat_type,
                    'Time_seconds': stat_type
                }).reset_index()
            
            stats['Lines_of_Code'] = stats['Mechanism'].map(loc_mapping)
            stats = stats[['Mechanism', 'Lines_of_Code', 'Clauses', 'Time_seconds']].sort_values('Mechanism')
            
            # Print table
            print(f"\n{'='*80}")
            print(f"MECHANISM SUMMARY TABLE ({stat_type.upper()} VALUES) - Scope 5, Steps 1-{steps}")
            print(f"{'='*80}")
            print()
            print("| Mechanism | Lines of Code | No. of Clauses | Solve time (sec) |")
            print("|-----------|---------------|-----------------|------------------|")
            
            for _, row in stats.iterrows():
                print(f"| {row['Mechanism']} | {row['Lines_of_Code']:,} | {row['Clauses']:,.0f} | {row['Time_seconds']:.3f} |")
            
            print()
            
            # Create LaTeX table
            filename = f"reports/mechanism_summary_{stat_type}_steps_{steps}.tex"
            create_latex_table(stats, filename, f"{stat_type.title()} values (Steps 1-{steps})")
    
    print("All LaTeX tables have been saved to the reports directory.")
    
    # Create detailed property tables
    create_detailed_property_tables(filtered_data)

def create_detailed_property_tables(filtered_data):
    """Create detailed tables showing each property individually."""
    
    # Get all unique properties
    properties = {
        'Simple': ['c_srp1', 'c_srp2', 'c_srp3', 'c_srp4'],
        'Forced Queue': ['c_fqp1', 'c_fqp2', 'c_fqp3', 'c_fqp4', 'c_fqp5', 'c_fqp6'],
        'Blacklist': ['c_bp1', 'c_bp2', 'c_bp3', 'c_bp4', 'c_bp5', 'c_blacklist_prop_all_censored'],
        'Upgradeability': ['c_up1', 'c_up2', 'c_up3', 'c_up4']
    }
    
    step_ranges = [5, 10]
    
    for steps in step_ranges:
        print(f"\n{'='*80}")
        print(f"DETAILED PROPERTY TABLE - Scope 5, Steps 1-{steps}")
        print(f"{'='*80}")
        print()
        print("| Mechanism | Property | No. of Clauses | Solve time (sec) |")
        print("|-----------|----------|-----------------|------------------|")
        
        for mechanism, prop_list in properties.items():
            for prop in prop_list:
                # Filter data for this specific property and step range
                prop_data = filtered_data[
                    (filtered_data['Command'].str.contains(prop)) & 
                    (filtered_data['Step_num'] <= steps)
                ]
                
                if not prop_data.empty:
                    total_clauses = prop_data['Clauses'].sum()
                    total_time = prop_data['Time_seconds'].sum()
                    print(f"| {mechanism} | {prop} | {total_clauses:,.0f} | {total_time:.3f} |")
        
        print()
        
        # Create LaTeX table for detailed properties
        create_detailed_latex_table(filtered_data, properties, steps, f"reports/detailed_properties_steps_{steps}.tex")
    
    print("Detailed property LaTeX tables have been saved to the reports directory.")

def create_detailed_latex_table(filtered_data, properties, steps, filename):
    """Create a LaTeX table for detailed properties."""
    
    latex_content = r"""\begin{table}[htbp]
\centering
\begin{tabular}{|l|l|c|c|}
\hline
\textbf{Mechanism} & \textbf{Property} & \textbf{No. of Clauses} & \textbf{Solve time (sec)} \\
\hline
"""
    
    for mechanism, prop_list in properties.items():
        for prop in prop_list:
            # Filter data for this specific property and step range
            prop_data = filtered_data[
                (filtered_data['Command'].str.contains(prop)) & 
                (filtered_data['Step_num'] <= steps)
            ]
            
            if not prop_data.empty:
                total_clauses = prop_data['Clauses'].sum()
                total_time = prop_data['Time_seconds'].sum()
                latex_content += f"{mechanism} & {prop} & {total_clauses:,} & {total_time:.3f} \\\\\n"
    
    latex_content += r"""\hline
\end{tabular}
\caption{Detailed property analysis (Scope 5, Steps 1-""" + str(steps) + r""")}
\label{tab:detailed_properties_steps_""" + str(steps) + r"""}
\end{table}"""
    
    with open(filename, 'w') as f:
        f.write(latex_content)
    
    print(f"Detailed property LaTeX table saved as '{filename}'")
    
def create_latex_table(data, filename, caption_suffix=""):
    """Create a LaTeX table similar to the provided example."""
    
    # Generate label from filename
    label = filename.replace('reports/', '').replace('.tex', '').replace('/', '_')
    
    latex_content = r"""\begin{table}[htbp]
\centering
\begin{tabular}{|l|c|c|c|}
\hline
\textbf{Mechanism} & \textbf{Lines of code} & \textbf{No. of Clauses} & \textbf{Solve time (sec)} \\
\hline
"""
    
    for _, row in data.iterrows():
        mechanism = row['Mechanism']
        loc = int(row['Lines_of_Code'])
        clauses = int(row['Clauses'])
        time = row['Time_seconds']
        
        latex_content += f"{mechanism} & {loc:,} & {clauses:,} & {time:.3f} \\\\\n"
    
    latex_content += f"""\\hline
\\end{{tabular}}
\\caption{{Mechanism summary using {caption_suffix} (Scope 5)}}
\\label{{tab:{label}}}
\\end{{table}}"""
    
    with open(filename, 'w') as f:
        f.write(latex_content)
    
    print(f"LaTeX table saved as '{filename}'")

def create_publication_plot():
    """Create a publication-quality plot showing execution time vs steps."""
    
    # Load data for both scopes
    scope5_data = load_results_data("results/results_5_10")
    scope10_data = load_results_data("results/results_10_10")
    
    if scope5_data.empty or scope10_data.empty:
        print("Error: Could not load data from results directories")
        return
    
    # Set up the plot style for publication
    plt.style.use('default')
    
    # Create figure with appropriate size for one column in a double-column paper
    # Typical column width is about 3.5 inches
    fig, ax = plt.subplots(figsize=(3.5, 2.8))
    
    # Define colors that are colorblind-friendly
    colors = ['#1f77b4', '#ff7f0e']  # Blue and orange
    markers = ['o', 's']  # Circle and square
    
    # Process data for each scope
    scopes = [5, 10]
    all_data = [scope5_data, scope10_data]
    
    for i, (scope, data) in enumerate(zip(scopes, all_data)):
        # Group by step number and calculate statistics
        step_stats = data.groupby('Step_num')['Time_seconds'].agg(['mean', 'std', 'min', 'max']).reset_index()
        
        # Plot mean line
        ax.plot(step_stats['Step_num'], step_stats['mean'], 
                color=colors[i], marker=markers[i], linewidth=2, 
                markersize=5, label=f'Scope {scope}')
        
        # Add shaded area for min-max range
        ax.fill_between(step_stats['Step_num'], step_stats['min'], step_stats['max'], 
                       color=colors[i], alpha=0.2, edgecolor='none')
    
    # Customize the plot
    ax.set_xlabel('Steps', fontsize=10)
    ax.set_ylabel('Execution Time (seconds)', fontsize=10)
    
    # Set axis limits and ticks
    ax.set_xlim(0.5, 10.5)
    ax.set_xticks(range(1, 11))
    ax.set_yscale('log')  # Use log scale for better visualization
    
    # Set y-axis ticks to show only main log values
    ax.set_yticks([0.1, 1, 10, 100, 1000, 10000])
    ax.set_yticklabels(['$10^{-1}$', '$10^0$', '$10^1$', '$10^2$', '$10^3$', '$10^4$'])
    
    # Disable minor ticks completely
    ax.yaxis.set_minor_locator(plt.NullLocator())
    
    # Add grid only for major ticks (log values and step values)
    ax.grid(True, alpha=0.3, which='major')
    ax.grid(False, which='minor')
    
    # Add legend
    ax.legend(frameon=True, fancybox=False, shadow=False, 
             loc='upper left', fontsize=9)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the plot
    plt.savefig('reports/alloy_verification_performance.pdf', 
                dpi=300, bbox_inches='tight', format='pdf')
    plt.savefig('reports/alloy_verification_performance.png', 
                dpi=300, bbox_inches='tight', format='png')
    
    print("Plot saved as 'reports/alloy_verification_performance.pdf' and 'reports/alloy_verification_performance.png'")
    
    # Print detailed statistics tables
    print("\n" + "="*80)
    print("DETAILED STATISTICS TABLES")
    print("="*80)
    
    for scope, data in zip(scopes, all_data):
        print(f"\n## Scope {scope}")
        print()
        
        # Calculate statistics for each step
        step_stats = data.groupby('Step_num').agg({
            'Time_seconds': ['min', 'max', 'mean', 'median'],
            'Clauses': ['min', 'max', 'mean', 'median']
        }).round(2)
        
        # Flatten column names
        step_stats.columns = ['_'.join(col).strip() for col in step_stats.columns.values]
        
        # Print execution time table
        print("### Execution Time (seconds)")
        print()
        print("| Step | Min | Max | Mean | Median |")
        print("|------|-----|-----|------|--------|")
        for step in sorted(data['Step_num'].unique()):
            stats = step_stats.loc[step]
            print(f"| {step} | {stats['Time_seconds_min']:.2f} | {stats['Time_seconds_max']:.2f} | {stats['Time_seconds_mean']:.2f} | {stats['Time_seconds_median']:.2f} |")
        
        print()
        print("### Number of Clauses")
        print()
        print("| Step | Min | Max | Mean | Median |")
        print("|------|-----|-----|------|--------|")
        for step in sorted(data['Step_num'].unique()):
            stats = step_stats.loc[step]
            print(f"| {step} | {stats['Clauses_min']:,.0f} | {stats['Clauses_max']:,.0f} | {stats['Clauses_mean']:,.0f} | {stats['Clauses_median']:,.0f} |")
        
        print()

def create_detailed_analysis():
    """Create additional analysis plots and statistics."""
    
    # Load data
    scope5_data = load_results_data("results/results_5_10")
    scope10_data = load_results_data("results/results_10_10")
    
    if scope5_data.empty or scope10_data.empty:
        return
    
    # Create a more detailed analysis
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(7, 5))
    
    # Plot 1: Box plot by step
    all_data = pd.concat([scope5_data, scope10_data], ignore_index=True)
    sns.boxplot(data=all_data, x='Step_num', y='Time_seconds', hue='Scope', ax=ax1)
    ax1.set_title('Execution Time Distribution by Step')
    ax1.set_yscale('log')
    
    # Plot 2: Variables vs Time
    ax2.scatter(scope5_data['Vars'], scope5_data['Time_seconds'], 
                alpha=0.6, label='Scope 5', color='blue')
    ax2.scatter(scope10_data['Vars'], scope10_data['Time_seconds'], 
                alpha=0.6, label='Scope 10', color='orange')
    ax2.set_xlabel('Variables')
    ax2.set_ylabel('Time (seconds)')
    ax2.set_title('Variables vs Execution Time')
    ax2.set_yscale('log')
    ax2.legend()
    
    # Plot 3: Clauses vs Time
    ax3.scatter(scope5_data['Clauses'], scope5_data['Time_seconds'], 
                alpha=0.6, label='Scope 5', color='blue')
    ax3.scatter(scope10_data['Clauses'], scope10_data['Time_seconds'], 
                alpha=0.6, label='Scope 10', color='orange')
    ax3.set_xlabel('Clauses')
    ax3.set_ylabel('Time (seconds)')
    ax3.set_title('Clauses vs Execution Time')
    ax3.set_yscale('log')
    ax3.legend()
    
    # Plot 4: Step complexity growth
    step5_stats = scope5_data.groupby('Step_num')[['Vars', 'Clauses']].mean()
    step10_stats = scope10_data.groupby('Step_num')[['Vars', 'Clauses']].mean()
    
    ax4.plot(step5_stats.index, step5_stats['Vars'], 'b-o', label='Scope 5 Vars')
    ax4.plot(step10_stats.index, step10_stats['Vars'], 'r-s', label='Scope 10 Vars')
    ax4.set_xlabel('Steps')
    ax4.set_ylabel('Variables')
    ax4.set_title('Variable Growth with Steps')
    ax4.legend()
    
    plt.tight_layout()
    plt.savefig('reports/detailed_analysis.pdf', dpi=300, bbox_inches='tight')
    print("Detailed analysis saved as 'reports/detailed_analysis.pdf'")

if __name__ == "__main__":
    print("Analyzing Alloy verification results...")
    create_comprehensive_mechanism_tables()
    create_publication_plot()
    create_detailed_analysis()
    print("Analysis complete!") 